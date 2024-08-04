# Alloy modelling for sound late static bindings


This repo models potential Hack language feautures for sound
[Late Static Bindings](https://www.php.net/manual/en/language.oop5.late-static-bindings.php).


Here's an example of a generated Hack program:

```
<?hh

abstract class C1 {
  public abstract static function abstractMethod(): void;
}

abstract class C2 extends C1 {
  public static function run(): void {
    static::abstractMethod(); // runtime fatal
  }
}

<<__EntryPoint>>
function main(): void {
    $cls = C2::class;
    $cls::run();
}
```



## How to Run

Prereqs:
- Get VSCode
- [the Alloy VSCode extension](https://marketplace.visualstudio.com/items?itemName=ArashSahebolamri.alloy) (much easier to use than plain Alloy Analyzer).
- Understand basics of the Alloy language, I found [this reference handy](https://alloy.readthedocs.io/en/latest/language/index.html)


Then:
- Open the hack.als file, and click the little tooltips above 'run' and 'check' commands:
    - `run` shows examples. If there are no examples found, it means you may have over-constrained: try commenting out facts.
    - `check` checks that there are no counterexamples. If there is a counterexample, it can be helpful to look at it and see what went wrong
- A window with Alloy will pop up, you may have to cmd-tab / alt-tab to it.
- The Viz tab shows a graph representation of the example or counterexample. Generally the examples and counterexample are easier to read as Hack code, though.
- Switch to the Txt tab in the analyzer
- copy all the text in the Txt tab
- paste it into a file and save the file
- run $REPO_ROOT/show $THE_FILE_NAME to see generated Hack code that is an example or counterexample.
- In the Alloy window, you can also click "new" to generate more counterexamples or examples
