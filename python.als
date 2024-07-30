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

abstract sig ClassName {
   upcast: set ClassName,
   names_class: Class
}
sig AbstractName, ConcreteName extends ClassName {}

sig Var {
   var_ty: ClassName,
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

fact "concrete classes cannot have abstract methods" {
  all class: ConcreteClass | no m: AbstractMethod | m in class.methods
}

fact "A variable must have come (transitively) from naming a class" {
  all v: Var | one class: Class | class in v.^var_points_to
}

// fact "all calls are resolved" { all call: Call | one m: Method | resolve[call] = m}
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

fact "typing: method must be statically visible. Example: in c.foo() (where c is a name for a class) foo must exist on that class" {
   all call: Call | one m: Method | static_resolve[call] = m
}

fact "typing: variable aliasing reflects subtyping" {
   // upper: supertype = (lower: subtype)
  all upper: Var | all lower: Var | lower in upper.var_points_to implies upper.var_ty in lower.var_ty.upcast
}


// --------------- New typing rules
fact "typing: aliasing rules" {
  all n1: ClassName | all n2: ClassName |
  n2 in n1.upcast implies (
	rule_abstract_covariant[n1, n2]
       or rule_concrete_covariant[n1, n2]
       or rule_concrete_to_abstract[n1, n2]
       or rule_abstract_to_concrete[n1, n2]
  )
}


pred rule_abstract_covariant[n1: ClassName, n2: ClassName] {
  n1 in AbstractName and n2 in AbstractName
  and descendent_of[n1, n2]
}

pred rule_concrete_covariant[n1: ClassName, n2: ClassName] {
  n1 in ConcreteName and n2 in ConcreteName
  and descendent_of[n1, n2]
}

pred rule_concrete_to_abstract[n1: ClassName, n2: ClassName] {
  n1 in ConcreteName and n2 in AbstractName
  and descendent_of[n1, n2]
}

pred rule_abstract_to_concrete[n1: ClassName, n2: ClassName] {
  n1 in AbstractName and n2 in ConcreteName
  and descendent_of[n1, n2] and n2.names_class in ConcreteClass
}


fact "typing: can't call abstract methods through AbstractName" {
  all call: Call |       all m: Method |
    (call.receiver.var_ty in AbstractName and
            m.method_name = call.call_method_name and m in static_resolve[call])
            implies m in ConcreteMethod
}

fact "A variable that points directly to a class can only have type ConcreteName if the class is concrete" {
   all v: Var | all class: Class |
   (v.var_points_to = class and v.var_ty in ConcreteName) implies class in ConcreteClass
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

pred descendent_of[descendent: ClassName, ancestor: ClassName] {
   ancestor.names_class in (descendent.names_class + descendent.names_class.^parent)
}


// ------------- pretty

fact "non-essential eta rule for ClassName that makes visualizations easier to read" {
   all n1: ClassName | all n2: ClassName |
   n1.names_class = n2.names_class
   and n1.upcast = n2.upcast implies n2 = n1
}

// ------------ ensure safety is non-trivial
fact "non-trivial" {
    some am: AbstractMethod | am in univ
    some call: Call | call in univ
}
// -------------run it
//run  {}
assert safe {  no c: Call | resolve[c] in AbstractMethod }
check safe for 3 but 1 Call




