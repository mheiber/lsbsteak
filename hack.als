// using custom build of alloy that enables custom visualizations
//@custom_visualization: ./show ./example.php
sig MethodName {}
// We treat __construct as a special static method.
// Constructors are like static methods from the *caller's* point of view
// since they are callable things defined on the class that don't require an instance
one sig __Construct in MethodName {}

abstract sig Method {
  method_name: one MethodName,
  concrete_class_attribute: lone ConcreteClassAttribute, // new attribute `<<__ConcreteClass>>`
}

// On the representation of methods of a class:
// - "inheritance" is when two classes share a method
// - "overriding" is when subclass has a class with the same name as the name of a class in the parent
abstract sig Class {
   methods: set Method,
   parent: lone Class
}

sig AbstractClass, ConcreteClass extends Class {}

sig ConcreteMethod extends Method {
  calls: set Call
}


sig AbstractMethod extends Method {}

sig Call {
   receiver: Receiver,
   call_method_name: MethodName,
   resolves_to: some Method, // note: static::foo() may resolve to methods of multiple classes
}

abstract sig Type {
   supertypes: set Type,
   names_class: Class
}

abstract sig Receiver {}

one sig StaticKeyword extends Receiver {}


/**
We are not modeling C::foo() directly, but you can see from 
the proposal that C::foo() is treated the same way as `(C::class)::foo()`.

We are not modeling `$cls = static::class;` and instead are only modeling
direct `static::foo()` calls. I suspect nothing hinges on this choice
*/
sig Var extends Receiver {
   var_ty: Type,
   var_points_to: one (Var + Class)
}

lone sig RuntimeFatal {
  fatal_at: Call
}

abstract sig TypeCheckerError {
   tc_error_at: some (Call + Var + Method)
}
lone sig TCMethodNotVisible,
  TCSubtypingError,
  TCCantCallAbstractMethodThroughClassName,
  TCCantCallConcreteClassMethodThroughClassName,
  TCCantOverrideNonConcreteClassMethodWithConcreteClassMethod,
  TCCanOnlyUseStaticAsConcreteInConcreteClassMethods
extends TypeCheckerError {}

//-------------new things
sig ClassName, ConcreteClassName extends Type {}
one sig ConcreteClassAttribute {}


// --------------- pre-existing well-formedness conditions

fact "no class is its own ancestor" {
   no c: Class | c in c.^parent
}

fact "all methods are in classes, all `MethodName`s name a method" {
  all m: Method | some c: Class | m in c.methods
  all mn: MethodName | some m: Method | m.method_name = mn
}

fact "all concrete classes have concrete constructors, no abstract classes have concrete constructors" {
  all c: Class | __Construct in (c.methods & ConcreteMethod).method_name iff c in ConcreteClass
}

fact "each static:: call is in a single method. And (ease of reading) other calls are outside methods" {
  all call: Call | call.receiver = StaticKeyword iff one m: Method | call in m.calls
}

fact "concrete classes cannot contain abstract methods" {
  no ConcreteClass.methods & AbstractMethod
}

fact "concrete classes must have implementations for all methods" {
    ConcreteClass.methods in ConcreteMethod
}

fact "a class must have all the method names of its parent" {
   all class: Class |
    (class.parent.methods.method_name - __Construct)
    in class.methods.method_name
}

fact "methods are only inherited from parents" {
  all disj class1, class2: Class |
  all m: class1.methods |
  m in class2.methods implies
      (class1 in class2.parent or class2 in class1.parent)
}

fact "A variable that names a class must have come (transitively) from naming a class" {
  all v: Var | one class: Class | class in v.^var_points_to
}

fact "method names are unique in a class" {
  all c: Class | all disj m1, m2: c.methods |
  disj[m1.method_name, m2.method_name]
}

// ---------------Runtime semantics

fact "dynamic method resolution" {
  all call: Call | call.resolves_to = resolve[call]
}

fact fatals { 
  all c: Call | resolve[c] in AbstractMethod iff c in RuntimeFatal.fatal_at
}

// --------------- Pre-existing type-checking

// Why is it not allowed to override a concrete method with an abstract method
// *unless* the abstract method happens to be a constructor? My understanding is now that
// constructors are inherently <<__ConcreteClass>>: we only allow constructing concrete classes.
// Aside:
// > This suggests an interesting alternative inheritance check that would also be sound while being more expressive:
//    "An abstract method cannot override a concrete method unless it is (<<__ConcreteClass>> or a constructor)."
fact "typing: an abstract method cannot override a concrete method UNLESS it's a constructor" {
    all class: Class | all m: class.methods, overridden: class.parent.methods |
    { m.method_name in overridden.method_name - __Construct // constructors are exempt
      overridden in ConcreteMethod
    } implies m in ConcreteMethod
}

// Example: in c.foo() (where c is a name for a class) foo must exist on that class"
fact "typing: method calls are to visible methods" { 
  TCMethodNotVisible.tc_error_at = 
   {call: Call | no static_resolve[call] }
}

fact "typing: variable aliasing reflects subtyping" {
  // var lower: subtype = .....
  // var upper: supertype = lower
  TCSubtypingError.tc_error_at =
  { lhs: Var | some rhs: Var & lhs.var_points_to |
    lhs.var_ty not in rhs.var_ty.supertypes
  }
}


// --------------- New typing rules
fact "typing: aliasing rules" {
  all t1, t2: Type |
  // all rules share the same conclusion
  t2 in t1.supertypes implies (
	rule_abstract_covariant[t1, t2]
       or rule_concrete_covariant[t1, t2]
       or rule_concrete_to_abstract[t1, t2]
      // or bad_rule_abstract_to_concrete[t1, t2] 
  )
}

/*
T inherits from U
----------------------------------
ClassName<T> <: ClassName<U>
*/
pred rule_abstract_covariant[t1, t2: Type] {
  t1 in ClassName and t2 in ClassName
  and inherits_from[t1, t2]
}

/*
T inherits from U
----------------------------------
ConcreteClassName<T> <: ConcreteClassName<U>
*/
pred rule_concrete_covariant[t1, t2: Type] {
  t1 in ConcreteClassName and t2 in ConcreteClassName
  and inherits_from[t1, t2]
}

/*
T inherits from U
----------------------------------
ConcreteClassName<T> <: ClassName<U>
*/
pred rule_concrete_to_abstract[t1, t2: Type] {
  t1 in ConcreteClassName and t2 in ClassName
  and inherits_from[t1, t2]
}

/*
UNSOUND: including here just for the neat counterexamples if you un-comment its usage above
*/
pred bad_rule_abstract_to_concrete[t1: Type, t2: Type] {
  {
    t1 in ClassName and t2 in ConcreteClassName
    inherits_from[t1, t2]
    t2.names_class in ConcreteClass
  }
}

fact "typing: can't call <<__ConcreteClass>> methods through ClassName" {
  TCCantCallConcreteClassMethodThroughClassName.tc_error_at =
  {call: Call |  {
      call.receiver in Var
      call.receiver.var_ty in ClassName
      call.static_resolve.has_concrete_class_attr
    }
  }
}

fact "typing: can't call abstract methods through ClassName" {
  TCCantCallAbstractMethodThroughClassName.tc_error_at =
  {call: Call |  {
      call.receiver in Var
      call.receiver.var_ty in ClassName
      call.static_resolve in AbstractMethod
    }
  }
}

fact typing_concrete_class_overriding {
  TCCantOverrideNonConcreteClassMethodWithConcreteClassMethod.tc_error_at =
  { m: Method | some overridden: m.~methods.parent.methods |
    { m.method_name = overridden.method_name
      m.has_concrete_class_attr
      not overridden.has_concrete_class_attr
    }

  }
}

// This subsumes the existing rules in Hack on where a constructor can be called from
fact "typing: Constructors implicitly have the <<__ConcreteClass>> attribute" {
  all m: Method | m.method_name = __Construct implies m.has_concrete_class_attr
}

fact "typing: can only call <<__ConcreteClass>> and abstract methods through StaticKeyword in a <<__ConcreteClass>> method" {
  TCCanOnlyUseStaticAsConcreteInConcreteClassMethods.tc_error_at = {
    call: Call | 
    let called_method = static_resolve[call] |
    {
      call.receiver = StaticKeyword
      (called_method.has_concrete_class_attr or called_method in AbstractMethod)
      not call.containing_method.has_concrete_class_attr
    }
  }
}

/*
C         C is a concrete class
-------------------------
C: ConcreteClassName<C>

*/
fact "C has type ConcreteClassName<C> when C is a concrete class" {
   all v: Var | all class: Class |
   (v.var_points_to = class and v.var_ty in ConcreteClassName) implies
   (class in ConcreteClass and v.var_ty.names_class = class)
}

/*
A          A is an abstract class
-------------------------
A: ClassName<A>
*/
fact "C has type ConcreteClassName<C> when C is a concrete class" {
   all v: Var | all class: Class |
   (v.var_points_to = class and v.var_ty in ClassName) implies
   (class in AbstractClass and v.var_ty.names_class = class)
}


// ------------- helpers

pred has_concrete_class_attr[m: Method] {
  ConcreteClassAttribute in m.concrete_class_attribute
}

fun resolve_var: Var -> Class {
    {v: Var, class: Class | class in v.^var_points_to}
}

fun resolve_var_call[v: Var, mn : MethodName]: some Method {
    {m: Method | m.method_name = mn and m in v.resolve_var.methods}
}


/**
We say that 'static' in method `m` resolves to all of the classes `C` s.t.
there is a call $receiver::m() that resolves to method `m` in `C`.

Some notes:
- We model inherited methods as shared between parent and child, so `static` in `static::m()` can resolve
to multiple classes
- We cannot represent `multi-hop static` cases like the following, since they would require `resolve_static_keyword` to be
recursive, which is not legal Alloy:

```
class A:
    static function foo():
      // static resolves to B due to call 1
      static::bar()        // call 2
    static function bar():
      // static resolves to B due to call 2
      static::bar()        // call 3

class B extends A:


A::foo() // call 1
```

This limitation doesn't matter, since we check the property
`static_always_resolves_to_a_concrete_class_in_concrete_class_methods`
No amount of calling methods on a `static` that points to a concrete class will make it stop pointing to a concrete
class.

*/
fun resolve_static_keyword: Method -> some Class {
  {m: Method, classes: m.~methods | 
    some call: Call|
          { 
            call.receiver in Var
            resolve_var_call[call.receiver, call.call_method_name] = m
            classes in call.receiver.resolve_var
          }

  }
}

fun resolve_static_keyword_call[method_containing_static: Method, callee_name : MethodName]: some Method {
          {m: Method |
          m.method_name = callee_name
          and m in resolve_static_keyword[method_containing_static].methods
              
                }
              
}


// c.foo() where c is a name for a class resolves to method foo of c *or a sub-class of c* at runtime
fun resolve[call: Call]: Method {
    call.receiver in Var implies
      resolve_var_call[call.receiver, call.call_method_name]
    else
      resolve_static_keyword_call[call.containing_method, call.call_method_name]
}

// c.foo() where c is a name for a class "statically resolves" to method foo of c (in the sense of "static type checking")
fun static_resolve[call: Call]: Method {
    {m: Method |
     (m.method_name = call.call_method_name and m in call.receiver.var_ty.names_class.methods)
     or       
      (StaticKeyword = call.receiver and (
              m.method_name = call.call_method_name and
              m in containing_class[call].methods
          ))
  }
}


fun containing_class[m: Method]: Class {
  {
    class: Class |
    m in class.methods and
    m not in class.^parent.methods
  }
}

fun containing_class[call: Call]: Class {
   call.containing_method.containing_class
}

fun containing_method[call: Call]: Method {
   {m: Method | call in m.calls }
}

pred inherits_from[descendent: Type, ancestor: Type] {
   ancestor.names_class in descendent.names_class.*parent
}


// --------------misc

// This simplification doesn't weaken our conclusions because once code has entered
// a constructor we know that the current runtime class is concrete: no more interesting
// interaction with names for classes or `abstract`. The simplification enables 
fact "consider only empty constructors (for simplicity)" {
  all m: Method | m.method_name = __Construct implies no m.calls
}


// ------------- pretty

fact "non-essential eta rule for ClassName that makes visualizations easier to read" {
   all t1, t2: ClassName |
   t1.names_class = t2.names_class
   and t1.supertypes = t2.supertypes implies t2 = t1
}


fact "non-essential eta rule for ConcreteClassName that makes visualizations easier to read" {
   all t1, t2: ConcreteClassName |
   t1.names_class = t2.names_class
   and t1.supertypes = t2.supertypes implies t2 = t1
}

// ------------predicates that can be used to show interesting examples
pred has_inherited_method {
  some m: Method | some disj c1, c2: Class | m in c1.methods and m in c2.methods
}

pred has_interesting_method_call {
  some call: Call | not (resolve[call] = static_resolve[call])
}

pred has_override {
  some m:  Method | some disj c1, c2: Class |
    { 
        c2 in c1.^parent
        m in c1.methods
        m not in c2.methods 
        m.method_name in c2.methods.method_name
    }
}
//---------------see examples

pred show { 
  // at least 1 method is abstract
  some AbstractMethod 
  and no TCSubtypingError
  and __Construct in Call.call_method_name
}

pred show_complicated {
  has_inherited_method
  has_interesting_method_call
  has_override
}

pred demo_tc_error[tc_error: TypeCheckerError] {
  one tc_error
  no (TypeCheckerError - tc_error)
  one RuntimeFatal
}

run  show for 4
run show_complicated for 4

/*
// important kind of example: variations of the following
class Parent: 
    static function m(): void {}

abstract class Child extends Parent:
    abstract static function abs: void {}
    <<__ConcreteClassName>>
    static function m: void {}
        static::abs; // 
    }

let $cls0 = Child::class; 
let $cls: classname<Parent> = $cls0;
$cls::m();
*/
run {
  some child: Class + Var
  , m: child.methods
  , abs: child.methods & AbstractMethod
  , static_call: m.calls
  , call_to_child: Call
  , overridden:  child.parent.methods
  |
  { 
    some disj v1, v2: Var | Var = v1  + v2
    Call = static_call + call_to_child
    Class = child + child.parent
    m.method_name = overridden.method_name
    m.method_name not in __Construct
    static_call.receiver = StaticKeyword
    static_call.call_method_name = abs.method_name
    call_to_child.receiver.var_ty.names_class = child.parent
    call_to_child.resolve = m
    one RuntimeFatal
    // try commenting/uncommenting different typing rules below
    // to see how they participate in the example
    no (
        TypeCheckerError
      - TCCantOverrideNonConcreteClassMethodWithConcreteClassMethod
      // - TCSubtypingError
      // - TCCantCallConcreteClassMethodThroughClassName
      // - TCCanOnlyUseStaticAsConcreteInConcreteClassMethods
    )
  }
} for 5

// see what each error does
run { demo_tc_error[ TCSubtypingError] } for 4
run { demo_tc_error[
  TCCantCallAbstractMethodThroughClassName
]} for 4
run { demo_tc_error[
  TCCantCallConcreteClassMethodThroughClassName
]} for 4
run { demo_tc_error[
  TCCantOverrideNonConcreteClassMethodWithConcreteClassMethod
]} for 4
run { demo_tc_error[
  TCCanOnlyUseStaticAsConcreteInConcreteClassMethods
]} for 4


// -------------check

assert static_always_resolves_to_a_concrete_class_in_concrete_class_methods {
   all m: Method |
   m.has_concrete_class_attr implies
      (resolve_static_keyword[m] in ConcreteClass
   or some TypeCheckerError.tc_error_at)

}
  
// If this property doesn't hold, we're only safe by accident
check static_always_resolves_to_a_concrete_class_in_concrete_class_methods

assert safe {
  some RuntimeFatal implies some TypeCheckerError
}

// takes ~50ms, checks for max 3 of each signature
check safe
// takes ~35 seconds
check safe for 4
// In Alloy options, I recommend selecting Glucose solver,
// then this runs in ~8 minutes on a Mac pro
check safe for 5 but 2 Call
