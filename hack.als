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
  lsbAttribute: LsbAttribute, // new attribute
}

sig AbstractMethod extends Method {}

sig Call {
   receiver: Receiver,
   call_method_name: MethodName,
   resolves_to: Method
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
sig AbstractType, ConcreteType extends Type {}
one sig LsbAttribute {}


// --------------- Boring well-formedness conditions

fact "no class is its own ancestor" {
   all c: Class | c not in c.^parent
}

fact "all methods are in classes, all calls are in methods, all `MethodName`s name a method" {
  all m: Method | some c: Class | m in c.methods
  all call: Call | some m: Method | call in m.calls
  all mn: MethodName | some m: Method | m.method_name = mn
}

fact "concrete classes cannot contain abstract methods" {
  all class: ConcreteClass | no m: AbstractMethod | m in class.methods
}


fact "concrete classes must have implementations for all methods" {
    all c: ConcreteClass | c.methods in ConcreteMethod
}

fact "a class must have all the method names of its parent" {
   all class: Class | all mn: class.parent.methods.method_name |
   mn in class.methods.method_name
}

fact "methods are only inherited from parents" {
  all disj class1, class2: Class |
  all m: class1.methods |
  m in class2.methods implies
      (class1 in class2.parent or class2 in class1.parent)
}

fact "A variable must have come (transitively) from naming a class" {
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
    all class: Class | all disj m1, overridden: (class + class.parent).methods | 
    overridden in ConcreteMethod implies m1 in ConcreteMethod
}

fact "typing: method calls are well-typed. Example: in c.foo() (where c is a name for a class) foo must exist on that class" {
   all call: Call | one m: Method | static_resolve[call] = m
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
       or rule_abstract_to_concrete[t1, t2]
  )
}

/*
T inherits from U
----------------------------------
AbstractType<T> <: AbstractType<U>
*/
pred rule_abstract_covariant[t1, t2: Type] {
  t1 in AbstractType and t2 in AbstractType
  and inherits_from[t1, t2]
}

/*
T inherits from U
----------------------------------
ConcreteType<T> <: ConcreteType<U>
*/
pred rule_concrete_covariant[t1, t2: Type] {
  t1 in ConcreteType and t2 in ConcreteType
  and inherits_from[t1, t2]
}

/*
T inherits from U
----------------------------------
ConcreteType<T> <: AbstractType<U>
*/
pred rule_concrete_to_abstract[t1, t2: Type] {
  t1 in ConcreteType and t2 in AbstractType
  and inherits_from[t1, t2]
}

/*
T inherits from U                       U is a concrete class
----------------------------------
AbstractType<T> <: ConcreteType<U>
*/
pred rule_abstract_to_concrete[t1: Type, t2: Type] {
  t1 in AbstractType and t2 in ConcreteType
  and inherits_from[t1, t2]
  // the last conjunct is important. Comment it out to see a counterexample showing unsafety
  and t2.names_class in ConcreteClass
}


fact "typing: can't call abstract methods through AbstractType" {
  all call: Call | 
    call.receiver.var_ty in AbstractType implies static_resolve[call] in ConcreteMethod
}


/*

C         C is a concrete class
-------------------------
C: ConcreteType<C>

*/
fact "C has type ConcreteType<C> when C is a concrete class" {
   all v: Var | all class: Class |
   (v.var_points_to = class and v.var_ty in ConcreteType) implies
   (class in ConcreteClass and v.var_ty.names_class = class)
}

/*
A          A is an abstract class
-------------------------
A: AbstractType<A>
*/
fact "C has type ConcreteType<C> when C is a concrete class" {
   all v: Var | all class: Class |
   (v.var_points_to = class and v.var_ty in AbstractType) implies
   (class in AbstractClass and v.var_ty.names_class = class)
}


fact "calls through StaticKeyword only allowed in concrete classes or in LSB methods" {
   all call: Call | call.receiver = StaticKeyword implies some method: Method |
   call in method.calls implies (containing_class[method] in ConcreteClass or method.is_lsb)
}

fact "lsb attribute only allowed in abstract concrete methods (for simplicity)" {
  all m: Method |
     m.is_lsb implies (containing_class[m] in AbstractClass and m in ConcreteMethod)
}

fact "all methods in abstract classes that use static must have the LSB Attribute" {
    all m: Method | (containing_class[m] in AbstractClass and StaticKeyword in m.calls.receiver) implies m.is_lsb
}

// TODO: restore this
//fact "all methods in abstract classes that call an LSB method must have the LSB Attribute" {
//   all m: Method | containing_class[m] in AbstractClass implies static_resolve[m.calls].is_lsb
//}

fact "cannot call LSB methods through variables of type AbstractType" {
  all call: Call | static_resolve[call].is_lsb and call.receiver in Var implies call.receiver.var_ty in ConcreteType
}



// ------------- helpers

pred is_lsb[m: Method] {
  LsbAttribute in m.lsbAttribute
}

fun resolve_var[v: Var]: one Class {
    {class: Class | class in v.^var_points_to} // guaranteed to be exactly one due to fact above
}

// c.foo() where c is a name for a class resolves to method foo of c *or a sub-class of c* at runtime
fun resolve[call: Call]: Method {
    {m: Method |
       (m.method_name = call.call_method_name and m in call.receiver.resolve_var.methods) 
      or  (StaticKeyword = call.receiver and (
         let class = containing_class[call] |
         let name = containing_method[call].method_name |
         m.method_name = name and m in (class + containing_class[m].^parent).methods
      ))
   }
}

// c.foo() where c is a name for a class "statically resolves" to method foo of c
fun static_resolve[call: Call]: Method {
    {m: Method |
         (m.method_name = call.call_method_name and m in call.receiver.var_ty.names_class.methods)
     or (StaticKeyword = call.receiver and (
              m.method_name = call.call_method_name and
              m in containing_class[call].methods
          ))
  }
}


fun containing_class[m: Method]: Class {
  {
     class: Class | m in class.methods and
     no ancestor: class.^parent | m in ancestor.methods
  }
}

fun containing_class[call: Call]: Class {
   call.containing_method.containing_class
}

fun containing_method[call: Call]: Method {
   {m: Method | m.method_name = call.call_method_name}
}

pred inherits_from[descendent: Type, ancestor: Type] {
   ancestor.names_class in (descendent.names_class + descendent.names_class.^parent)
}


// ------------- pretty

fact "non-essential eta rule for AbstractType that makes visualizations easier to read" {
   all t1, t2: AbstractType |
   t1.names_class = t2.names_class
   and t1.supertypes = t2.supertypes implies t2 = t1
}


fact "non-essential eta rule for ConcreteType that makes visualizations easier to read" {
   all t1, t2: ConcreteType |
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
  // TODO: comment the rest out. Interesting that this makes no instance found
  some call: Call | call.receiver = StaticKeyword and containing_class[call] in ConcreteClass
}

pred show_complicated {
  has_inherited_method
  has_interesting_method_call
  has_override
}

run  show for 3
// run show_complicated for 4

// -------------check

assert safe {  no c: Call | resolve[c] in AbstractMethod }
check safe
// check safe for 4
// check safe for 5
