





class AbstractClass0 {
    abstract static function m0(): void
}

class ConcreteClass extends AbstractClass0 {}
class AbstractClass1 extends ConcreteClass {}

<<__EntryPoint>>
function main(): void {
    let $v1: concrete_classname<AbstractClass1> = AbstractClass1::class;
    let $v0: concrete_classname<ConcreteClass> = v1;
    let $v2: concrete_classname<AbstractClass0> = v0;
    let $v2.m0();
}
