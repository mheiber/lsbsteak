//------------boring things
abstract sig Class {
   methods: set Method,
   parent: lone Class
}

sig AbstractClass, ConcreteClass extends Class {}

sig MethodName {}

abstract sig Method {
  method_name: one MethodName
}

sig ConcreteMethod extends Method {
  calls: set Call,
  use_static_attribute: lone UseStaticAttribute, // new attribute
}

sig AbstractMethod extends Method {}

sig Call {
   receiver: Receiver,
   call_method_name: MethodName,
   resolves_to: some Method, // static::foo() may resolve to methods of multiple classes
}

abstract sig Type {
   supertypes: set Type,
   names_class: Class
}


abstract sig Receiver {}

one sig StaticKeyword extends Receiver {}

sig Var extends Receiver {
   var_ty: Type,
   var_points_to: one (Var + Class)
}


//-------------new things
sig AbstractName, ConcreteName extends Type {}
one sig UseStaticAttribute {}


// --------------- Boring well-formedness conditions

fact "no class is its own ancestor" {
   no c: Class | c in c.^parent
}

fact "all methods are in classes, all `MethodName`s name a method" {
  all m: Method | some c: Class | m in c.methods
  all mn: MethodName | some m: Method | m.method_name = mn
}

fact "all static:: calls are in methods. And (for ease of reading) all other calls are outside methods" {
  all call: Call | call.receiver = StaticKeyword iff call in Method.calls
}

fact "concrete classes cannot contain abstract methods" {
  no ConcreteClass.methods & AbstractMethod
}

fact "concrete classes must have implementations for all methods" {
    ConcreteClass.methods in ConcreteMethod
}

fact "a class must have all the method names of its parent" {
   all class: Class |
    class.parent.methods.method_name
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
 

// --------------- Pre-existing, obvious type-checking

fact "typing: an abstract method cannot override a concrete method " {
    all class: Class | all m: class.methods, overridden: class.parent.methods |
    { m.method_name = overridden.method_name
      overridden in ConcreteMethod
    } implies m in ConcreteMethod
}

// Example: in c.foo() (where c is a name for a class) foo must exist on that class"
fact "typing: method calls are to visible methods" { 
   all call: Call | some m: Method | static_resolve[call] = m
}

fact "typing: variable aliasing reflects subtyping" {
  // var lower: subtype = .....
  // var upper: supertype = lower
  all upper, lower: Var | lower in upper.var_points_to implies upper.var_ty in lower.var_ty.supertypes
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
AbstractName<T> <: AbstractName<U>
*/
pred rule_abstract_covariant[t1, t2: Type] {
  t1 in AbstractName and t2 in AbstractName
  and inherits_from[t1, t2]
}

/*
T inherits from U
----------------------------------
ConcreteName<T> <: ConcreteName<U>
*/
pred rule_concrete_covariant[t1, t2: Type] {
  t1 in ConcreteName and t2 in ConcreteName
  and inherits_from[t1, t2]
}

/*
T inherits from U
----------------------------------
ConcreteName<T> <: AbstractName<U>
*/
pred rule_concrete_to_abstract[t1, t2: Type] {
  t1 in ConcreteName and t2 in AbstractName
  and inherits_from[t1, t2]
}

/*
UNSOUND: including here just for the neat counterexamples if you un-comment its usage abov
*/
pred bad_rule_abstract_to_concrete[t1: Type, t2: Type] {
  {
    t1 in AbstractName and t2 in ConcreteName
    inherits_from[t1, t2]
    t2.names_class in ConcreteClass
  }
}


fact "typing: can't call abstract or UseStatic methods through AbstractName" {
  all call: Call | 
    (call.receiver in Var and call.receiver.var_ty in AbstractName)
    implies (
      static_resolve[call] in ConcreteMethod
      and not static_resolve[call].use_static
    )
}

fact "typing: a UseStatic method cannot override a non-UseStatic method" {
    all class: Class | all m: class.methods, overridden: class.parent.methods |
    { m.method_name = overridden.method_name
      m.use_static
    } implies overridden.use_static
}

/*
C         C is a concrete class
-------------------------
C: ConcreteName<C>

*/
fact "C has type ConcreteName<C> when C is a concrete class" {
   all v: Var | all class: Class |
   (v.var_points_to = class and v.var_ty in ConcreteName) implies
   (class in ConcreteClass and v.var_ty.names_class = class)
}

/*
A          A is an abstract class
-------------------------
A: AbstractName<A>
*/
fact "C has type ConcreteName<C> when C is a concrete class" {
   all v: Var | all class: Class |
   (v.var_points_to = class and v.var_ty in AbstractName) implies
   (class in AbstractClass and v.var_ty.names_class = class)
}


fact "all methods that use static must have the UseStatic Attribute" {
    all m: Method | StaticKeyword in m.calls.receiver implies m.use_static
}



// ------------- helpers

pred use_static[m: Method] {
  UseStaticAttribute in m.use_static_attribute
}

fun resolve_var: Var -> Class {
    {v: Var, class: Class | class in v.^var_points_to}
}

fun resolve_var_call[v: Var, mn : MethodName]: some Method {
    {m: Method | m.method_name = mn and m in v.resolve_var.methods}
}


// TODO: overly restrictive. Had to hack around recursion limitation. revisit
fun resolve_static_keyword: Method -> some Class {
  {m: Method, classes: m.~methods | 
    some call: Call|
          call.receiver in Var and
            resolve_var_call[call.receiver, call.call_method_name] = m

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


// ------------- pretty

fact "non-essential eta rule for AbstractName that makes visualizations easier to read" {
   all t1, t2: AbstractName |
   t1.names_class = t2.names_class
   and t1.supertypes = t2.supertypes implies t2 = t1
}


fact "non-essential eta rule for ConcreteName that makes visualizations easier to read" {
   all t1, t2: ConcreteName |
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
//---------------show

pred show { 
  // at least 1 method is abstract
  some am: AbstractMethod | am in univ
}

pred show_complicated {
  has_inherited_method
  has_interesting_method_call
  has_override
}

run  show for 3
run show_complicated for 4

run {
  some abs_meth: AbstractMethod |
  some call: Call |
    {
      call.receiver = StaticKeyword
      call.call_method_name = abs_meth.method_name
      not call.containing_method.use_static

    } 
} 

run {
  some class: Class, call: class.methods.calls |
      {
        call.receiver in StaticKeyword
        call.call_method_name in (class.methods & AbstractMethod).method_name
        call.static_resolve in AbstractMethod
      }
} 
run {
  some class: AbstractClass, call: class.methods.calls | {
    call.receiver in StaticKeyword
  }
}
run {
  some call: Call, disj m1, m2: Method | (m1 + m2) in call.resolve
}

// -------------check

assert safe {  no c: Call | resolve[c] in AbstractMethod }
check safe
check safe for 4
check safe for 5
