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
  lsbAttribute: lone LsbAttribute,
}

one sig LsbAttribute {}

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
sig AbstractClassName, ConcreteClassName extends Type {}

abstract sig Receiver {}
sig Var extends Receiver {
   var_ty: Type,
   var_points_to: one (Var + Class)
}

one sig StaticKeyword extends Receiver {}

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

fact "concrete classes must have implementations for all methods" {
    all c: ConcreteClass |
    let method_names = (c + c.^parent).methods.method_name  |
    let implemented_methods = (c + c.^parent).methods & ConcreteMethod |
    method_names in implemented_methods.method_name
}

fact "A variable must have come (transitively) from naming a class" {
  all v: Var | one class: Class | class in v.^var_points_to
}

fact "method names are unique in a class" {
  all c: Class | all m1: Method | all m2: Method |
  m1 in c.methods and m1.method_name = m2.method_name implies m1 = m2 
}

fact "static keyword only allowed in methods" {
   all call: Call | call.receiver in StaticKeyword
   implies one method: ConcreteMethod | call in method.calls
}

// --------------- new well-formedness conditions
fact "lsb attribute only allowed in concrete methods of abstract classes" {
   all class: Class |
   all m: (ConcreteMethod & class.methods) |
   (LsbAttribute in m.lsbAttribute)
   implies class in AbstractClass
}
//
fact "lsb attribute required in methods of abstract classes that call through static keyword" {
   all class: AbstractClass |
   all m: (ConcreteMethod & class.methods) |
   all call: m.calls |
   (StaticKeyword = call.receiver)
   implies LsbAttribute in m.lsbAttribute
}

fact "lsb attribute required in methods of abstract classes that call LSB methods" {
   all class: AbstractClass |
   all m: (ConcreteMethod & class.methods) |
   all call: m.calls |
   (LsbAttribute in static_resolve[call].lsbAttribute)
   implies LsbAttribute in m.lsbAttribute
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
AbstractClassName<T> <: AbstractClassName<U>
*/
pred rule_abstract_covariant[t1: Type, t2: Type] {
  t1 in AbstractClassName and t2 in AbstractClassName
  and inherits_from[t1, t2]
}

/*
T inherits from U
----------------------------------
ConcreteClassName<T> <: ConcreteClassName<U>
*/
pred rule_concrete_covariant[t1: Type, t2: Type] {
  t1 in ConcreteClassName and t2 in ConcreteClassName
  and inherits_from[t1, t2]
}

/*
T inherits from U
----------------------------------
ConcreteClassName<T> <: AbstractClassName<U>
*/
pred rule_concrete_to_abstract[t1: Type, t2: Type] {
  t1 in ConcreteClassName and t2 in AbstractClassName
  and inherits_from[t1, t2]
}

/*
T inherits from U                       U is a concrete class
----------------------------------
AbstractClassName<T> <: ConcreteClassName<U>
*/
pred rule_abstract_to_concrete[t1: Type, t2: Type] {
  t1 in AbstractClassName and t2 in ConcreteClassName
  and inherits_from[t1, t2]
  // the last conjunct is important. Comment it out to see a counterexample showing unsafety
  and t2.names_class in ConcreteClass
}


fact "typing: can't call abstract methods through AbstractClassName" {
  all call: Call |       all m: Method |
    (call.receiver.var_ty in AbstractClassName and
            m.method_name = call.call_method_name and m in static_resolve[call])
            implies m in ConcreteMethod
}

/*

C         C is a concrete class
-------------------------
C: ConcreteClassName<C>

*/
fact "C has type ConcreteClassName<C> when C is a concrete class" {
   all v: Var | all class: Class |
   (v.var_points_to = class and v.var_ty in ConcreteClassName) implies class in ConcreteClass
}

/*
A          A is an abstract class
-------------------------
A: AbstractClassName<A>
*/
fact "C has type ConcreteClassName<C> when C is a concrete class" {
   all v: Var | all class: Class |
   (v.var_points_to = class and v.var_ty in AbstractClassName) implies class in AbstractClass
}

// ------------- helpers

fun resolve_var[v: Var]: some Class {
     {class: Class | class in v.^var_points_to}
}

/*
class A:
     a():

class B extends A:
     m():
        static::a()

class C extends B:

C.m()

*/

fun resolve_static[call: Call]: some Method {
   {m: Method | m.method_name = call.call_method_name and
   (some containingClass: Class | some v: Var | v.resolve_var = containingClass 
    
   (some runtime_class: Class | runtime_class in ))
}

// c.foo() where c is a name for a class resolves to method foo of c *or a sub-class of c* at runtime
fun resolve[call: Call]: some Method {
    {m: Method | m.method_name = call.call_method_name and m in call.receiver.resolve_var.methods}
+  call.resolve_static.methods
}

// c.foo() where c is a name for a class "statically resolves" to method foo of c
fun static_resolve[call: Call]: Method {
    {m: Method | m.method_name = call.call_method_name and m in call.receiver.var_ty.names_class.methods}
}

pred inherits_from[descendent: Type, ancestor: Type] {
   ancestor.names_class in (descendent.names_class + descendent.names_class.^parent)
}


// ------------- pretty

fact "non-essential eta rule for AbstractClassName that makes visualizations easier to read" {
   all t1: AbstractClassName | all t2: AbstractClassName |
   t1.names_class = t2.names_class
   and t1.supertypes = t2.supertypes implies t2 = t1
}


fact "non-essential eta rule for ConcreteClassName that makes visualizations easier to read" {
   all t1: ConcreteClassName | all t2: ConcreteClassName |
   t1.names_class = t2.names_class
   and t1.supertypes = t2.supertypes implies t2 = t1
}

// ------------make it interesting
pred show {
    some am: AbstractMethod | am in univ
    some call: Call | call in univ
}
// -------------commands
// run  show
assert safe {  no c: Call | resolve[c] in AbstractMethod }
check safe
// check safe for 4 // up to 4 instances for every signature
// check safe for 10




