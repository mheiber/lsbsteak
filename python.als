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
  calls: set Call
}

sig AbstractMethod extends Method {}

sig Call {
   receiver: Var,
   call_method_name: MethodName,
   resolves_to: Method
}

abstract sig Type {
   supertypes: set Type,
   names_class: Class
}
sig AbstractType, ConcreteType extends Type {}

sig Var {
   var_ty: Type,
   var_points_to: one (Var + Class)
}


// --------------- Boring well-formedness conditions

fact "no class is its own ancestor" {
   all c: Class | c not in c.^parent
}

fact "all methods are in classes, all calls are in methods, all `MethodName`s are used" {
  all m: Method | some c: Class | m in c.methods
  all call: Call | some m: Method | call in m.calls
  all mn: MethodName | some m: Method | m.method_name = mn
}

fact "concrete classes cannot have direct abstract methods" {
  all class: ConcreteClass | no m: AbstractMethod | m in class.methods
}

fact "methods are inherited" {
   all class: Class | all mn: class.^parent.methods.method_name |
   mn in class.methods.method_name
}

fact "concrete classes must have implementations for all methods" {
    all c: ConcreteClass |
    c.methods in ConcreteMethod
}

fact "A variable must have come (transitively) from naming a class" {
  all v: Var | one class: Class | class in v.^var_points_to
}

fact "method names are unique in a class" {
  all c: Class | all m1: Method | all m2: Method |
  m1 in c.methods and m1.method_name = m2.method_name implies m1 = m2 
}

// ---------------Runtime semantics

fact "dynamic method resolution" {
  all call: Call| call.resolves_to = resolve[call]
}
 

// --------------- Pre-existing, obvious type-checking

fact "typing: an abstract method cannot override a concrete method " {
    all m1: Method | all overridden: Method | all c: Class |
    m1 in c.methods
    and m1.method_name = overridden.method_name
    and overridden in c.^parent.methods
    and overridden in ConcreteMethod
    implies m1 in ConcreteMethod
}

fact "typing: method calls are well-typed. Example: in c.foo() (where c is a name for a class) foo must exist on that class" {
   all call: Call | one m: Method | static_resolve[call] = m
}

fact "typing: variable aliasing reflects subtyping" {
  // var lower: subtype = .....
  // var upper: supertype = lower
  all upper: Var | all lower: Var | lower in upper.var_points_to implies upper.var_ty in lower.var_ty.supertypes
}


// --------------- New typing rules
fact "typing: aliasing rules" {
  all t1: Type | all t2: Type |
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
pred rule_abstract_covariant[t1: Type, t2: Type] {
  t1 in AbstractType and t2 in AbstractType
  and inherits_from[t1, t2]
}

/*
T inherits from U
----------------------------------
ConcreteType<T> <: ConcreteType<U>
*/
pred rule_concrete_covariant[t1: Type, t2: Type] {
  t1 in ConcreteType and t2 in ConcreteType
  and inherits_from[t1, t2]
}

/*
T inherits from U
----------------------------------
ConcreteType<T> <: AbstractType<U>
*/
pred rule_concrete_to_abstract[t1: Type, t2: Type] {
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
  all call: Call |       all m: Method |
    (call.receiver.var_ty in AbstractType and
            m.method_name = call.call_method_name and m in static_resolve[call])
            implies m in ConcreteMethod
}

/*

C         C is a concrete class
-------------------------
C: ConcreteType<C>

*/
fact "C has type ConcreteType<C> when C is a concrete class" {
   all v: Var | all class: Class |
   (v.var_points_to = class and v.var_ty in ConcreteType) implies class in ConcreteClass
}

/*
A          A is an abstract class
-------------------------
A: AbstractType<A>
*/
fact "C has type ConcreteType<C> when C is a concrete class" {
   all v: Var | all class: Class |
   (v.var_points_to = class and v.var_ty in AbstractType) implies class in AbstractClass
}

// ------------- helpers

fun resolve_var[v: Var]: one Class {
    {class: Class | class in v.^var_points_to} // guaranteed to be exactly one due to fact above
}

// c.foo() where c is a name for a class resolves to method foo of c *or a sub-class of c* at runtime
fun resolve[call: Call]: Method {
    {m: Method | m.method_name = call.call_method_name and m in call.receiver.resolve_var.methods}
}

// c.foo() where c is a name for a class "statically resolves" to method foo of c
fun static_resolve[call: Call]: Method {
    {m: Method | m.method_name = call.call_method_name and m in call.receiver.var_ty.names_class.methods}
}

pred inherits_from[descendent: Type, ancestor: Type] {
   ancestor.names_class in (descendent.names_class + descendent.names_class.^parent)
}


// ------------- pretty

fact "non-essential eta rule for AbstractType that makes visualizations easier to read" {
   all t1: AbstractType | all t2: AbstractType |
   t1.names_class = t2.names_class
   and t1.supertypes = t2.supertypes implies t2 = t1
}


fact "non-essential eta rule for ConcreteType that makes visualizations easier to read" {
   all t1: ConcreteType | all t2: ConcreteType |
   t1.names_class = t2.names_class
   and t1.supertypes = t2.supertypes implies t2 = t1
}

// ------------make it interesting
pred show {
    some am: AbstractMethod | am in univ
    some call: Call | call in univ
}
// -------------commands
run  show
assert safe {  no c: Call | resolve[c] in AbstractMethod }
check safe for 4 // up to 4 instances for every signature
// check safe for 10




