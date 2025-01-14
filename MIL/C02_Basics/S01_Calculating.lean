import MIL.Common
import Mathlib.Data.Real.Basic
/- OMIT:
Calculating
-----------
OMIT. -/

/- TEXT:
計算
-----------
TEXT. -/


/- OMIT:
We generally learn to carry out mathematical calculations
without thinking of them as proofs.
But when we justify each step in a calculation,
as Lean requires us to do,
the net result is a proof that the left-hand side of the calculation
is equal to the right-hand side.
OMIT. -/

/- TEXT:
私たちは通常，数学的な計算のことを証明と考えずに行うよう学びます．しかし，計算の各ステップを正当化する必要があるLeanの要件に従うと，計算はつまるところ左辺が右辺に等しいという証明であるという結論に行き着きます．

TEXT. -/


/- OMIT:
.. index:: rewrite, rw, tactics ; rw and rewrite
OMIT. -/

/- TEXT:
.. index:: rewrite, rw, tactics ; rw and rewrite

TEXT. -/

/- OMIT:
In Lean, stating a theorem is tantamount to stating a goal,
namely, the goal of proving the theorem.
Lean provides the rewriting tactic ``rw``,
to replace the left-hand side of an identity by the right-hand side
in the goal. If ``a``, ``b``, and ``c`` are real numbers,
``mul_assoc a b c``  is the identity ``a * b * c = a * (b * c)``
and ``mul_comm a b`` is the identity ``a * b = b * a``.
Lean provides automation that generally eliminates the need
to refer the facts like these explicitly,
but they are useful for the purposes of illustration.
In Lean, multiplication associates to the left,
so the left-hand side of ``mul_assoc`` could also be written ``(a * b) * c``.
However, it is generally good style to be mindful of Lean's
notational conventions and leave out parentheses when Lean does as well.

Let's try out ``rw``.
OMIT. -/


/- TEXT:
Leanにおいて，定理を述べるということは，その定理を証明するというゴールを述べることと同等です．Leanには，ゴールの左辺をそれと等しい右辺に置き換えるタクティクである ``rw`` が存在します．``a`` ， ``b``， ``c`` が実数の時， ``mul_assoc a b c`` は ``a * b * c = a * (b * c)`` という恒等式であり， ``mul_comm a b`` は ``a * b = b * a`` という恒等式を表しています．Lean には自動化の仕組みがあるので，こうして明示的に事実を参照する必要はないのですが，説明のためには ``rw`` が便利です．Leanにおいて，掛け算は左側から計算されます．よって左側にある ``mul_assoc`` は ``(a * b) * c`` と書くことも可能です．しかしながら，一般的にはLeanの表記規則に倣い，Leanが括弧を省略する場合は括弧を省略するのが良いとされるスタイルです．
``rw`` を試してみましょう！

TEXT. -/

/- OMIT:
.. index:: real numbers
OMIT. -/

/- TEXT:
.. index:: 実数
TEXT. -/


-- An example.
-- QUOTE:
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]
-- QUOTE.

/- OMIT:
The ``import`` lines at the beginning of the associated examples file
import the theory of the real numbers from Mathlib, as well as useful automation.
For the sake of brevity,
we generally suppress information like this in the textbook.

You are welcome to make changes to see what happens.
You can type the ``ℝ`` character as ``\R`` or ``\real``
in VS Code.
The symbol doesn't appear until you hit space or the tab key.
If you hover over a symbol when reading a Lean file,
VS Code will show you the syntax that can be used to enter it.
If you are curious to see all available abbreviations, you can hit Ctrl-Shift-P
and then type abbreviations to get access to the ``Lean 4: Show all abbreviations`` command.
If your keyboard does not have an easily accessible backslash,
you can change the leading character by changing the
``lean4.input.leader`` setting.

.. index:: proof state, local context, goal

When a cursor is in the middle of a tactic proof,
Lean reports on the current *proof state* in the
*Lean Infoview* window.
As you move your cursor past each step of the proof,
you can see the state change.
A typical proof state in Lean might look as follows:

.. code-block::

    1 goal
    x y : ℕ,
    h₁ : Prime x,
    h₂ : ¬Even x,
    h₃ : y > x
    ⊢ y ≥ 4

The lines before the one that begins with ``⊢`` denote the *context*:
they are the objects and assumptions currently at play.
In this example, these include two objects, ``x`` and ``y``,
each a natural number.
They also include three assumptions,
labelled ``h₁``, ``h₂``, and ``h₃``.
In Lean, everything in a context is labelled with an identifier.
You can type these subscripted labels as ``h\1``, ``h\2``, and ``h\3``,
but any legal identifiers would do:
you can use ``h1``, ``h2``, ``h3`` instead,
or ``foo``, ``bar``, and ``baz``.
The last line represents the *goal*,
that is, the fact to be proved.
Sometimes people use *target* for the fact to be proved,
and *goal* for the combination of the context and the target.
In practice, the intended meaning is usually clear.

Try proving these identities,
in each case replacing ``sorry`` by a tactic proof.
With the ``rw`` tactic, you can use a left arrow (``\l``)
to reverse an identity.
For example, ``rw [← mul_assoc a b c]``
replaces ``a * (b * c)`` by ``a * b * c`` in the current goal. Note that
the left-pointing arrow refers to going from right to left in the identity provided
by ``mul_assoc``, it has nothing to do with the left or right side of the goal.
OMIT. -/

/- TEXT:
例題ファイルの先頭にある ``import`` 行は，Mathlib から実数の理論や便利なオートメーションをインポートします．簡潔のため，本書では一般的にこのような情報は省略します．自由に変更して，何が起こるのか確認してみてください．VSCodeでは ``ℝ`` を ``\R`` または ``\real`` で入力することができます． ``ℝ`` 記号はスペースかタブキーを押すまで表示されません．Leanファイルを読むときに記号の上にカーソルを置くと，VSCodeはその記号を入力するために使用できる構文を表示します．使用可能な略語をすべて見たい場合は，Ctrl+Shift+P を押した後に ``abbreviations`` と入力すれば， ``Lean 4: Show all abbreviations`` コマンドにアクセスできます．キーボードにバックスラッシュがない場合は， ``lean4.input.leader`` の設定を変更することで，先頭の文字を変更することができます．

.. index:: proof state, local context, goal

カーソルがタクティクスタイルの証明の途中にあるとき，Lean は現在の証明の状態を **Lean Infoview** ウィンドウに表示します．カーソルを動かすと，状態が変化するのがわかります．Leanの典型的な証明の状態は以下のようになります：

.. code-block::

    1 goal
    x y : ℕ,
    h₁ : Prime x,
    h₂ : ¬Even x,
    h₃ : y > x
    ⊢ y ≥ 4

``⊢`` で始まる行の前の行は **コンテキスト** を表しています．この例では，2つの変数 ``x`` と ``y`` が含まれており，それぞれが自然数です．また， ``h₁`` ， ``h₂`` ， ``h₃`` とラベル付けされた3つの仮定も含まれます．Leanでは，コンテキスト内のすべてのものに  ``h\1``, ``h\2`` などのような識別子が付きます．文法的に正しい識別子であればどのような識別子でも使用することができます．代わりに ``h\3``，``\h1`` ， ``\h2`` ， ``\h3`` ， ``h1`` ， ``h2``， ``h3`` や ``foo`` ， ``bar`` ， ``baz`` などを使うことが可能です．最後の行はゴール，つまり証明されるべき事実を表しています．証明されるべき事実を **target** ，コンテキストとゴールの組み合わせを **goal** と呼ぶこともあります．実際には，意図する意味はたいてい明らかです．それぞれのケースで ``sorry`` をタクティクを用いた証明に置き換えて，以下の恒等式を証明してみましょう． ``rw`` タクティクを使う際に，左矢印 ( ``\l`` ) を使うことで右辺を左辺に書き換えることができます．例えば， ``rw [← mul_assoc a b c]`` は現在のゴールを ``a * (b * c)`` から ``a * b * c`` に置き換えます．左向きの矢印 ← は ``mul_assoc`` が提供する等式の向きを変えることを意味し，ゴールの左辺や右辺に影響を与えないことに注意してください．
TEXT. -/

-- Try these.
-- QUOTE:
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

/- OMIT:
You can also use identities like ``mul_assoc`` and ``mul_comm`` without arguments.
In this case, the rewrite tactic tries to match the left-hand side with
an expression in the goal,
using the first pattern it finds.
OMIT. -/

/- TEXT:
``mul_assoc`` や ``mul_comm`` のような恒等式を引数なしで使うことも可能です．この場合， ``rw`` タクティクは最初に見つけたパターンを使って，左辺とゴールの式をマッチさせようとします．
TEXT. -/

-- An example.
-- QUOTE:
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]
-- QUOTE.

/- OMIT:
You can also provide *partial* information.
For example, ``mul_comm a`` matches any pattern of the form
``a * ?`` and rewrites it to ``? * a``.
Try doing the first of these examples without
providing any arguments at all,
and the second with only one argument.
OMIT. -/

/- TEXT:
*部分的な情報* を提供することも可能です．例えば， ``mul_comm a`` は ``a * ?`` という形の全てのパターンにマッチして，それを ``? * a`` に書き換えます．1個めの例は1つも引数を使用せずに，2個めの例は1つの引数のみを使用して証明してみましょう．
TEXT. -/


/- OMIT:
/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
OMIT. -/


-- QUOTE:
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]

/- OMIT:
You can also use ``rw`` with facts from the local context.
OMIT. -/
/- TEXT:
ローカルコンテキストにある事実を ``rw`` で使用することも可能です．
TEXT. -/

-- Using facts from the local context.
-- QUOTE:
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
-- QUOTE.

/- OMIT:
Try these, using the theorem ``sub_self`` for the second one:
OMIT. -/

/- TEXT:
2番目の命題には ``sub_self`` を使用してみてください．
TEXT. -/

-- QUOTE:
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]

/- OMIT:
Multiple rewrite commands can be carried out with a single command,
by listing the relevant identities separated by commas inside the square brackets.
OMIT. -/

/- TEXT:
関連する等式を角括弧の中にカンマで区切って列挙すると，複数の書き換えコマンドを1つのコマンドで実行することが可能です．
TEXT. -/

-- QUOTE:
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
-- QUOTE.

/- OMIT:
You still see the incremental progress by placing the cursor after
a comma in any list of rewrites.

Another trick is that we can declare variables once and for all outside
an example or theorem. Lean then includes them automatically.
OMIT. -/

/- TEXT:
書き換えのリストのカンマの後にカーソルを置くと，次の段階が表示されます．もう1つの小技として，例や定理の外側で変数を一度に宣言できます． そうすると Lean がそれを自動的に取り込みます．
TEXT. -/

section

-- QUOTE:
variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
-- QUOTE.

end

/- OMIT:
Inspection of the tactic state at the beginning of the above proof
reveals that Lean indeed included all variables.
We can delimit the scope of the declaration by putting it
in a ``section ... end`` block.
Finally, recall from the introduction that Lean provides us with a
command to determine the type of an expression:
OMIT. -/

/- TEXT:
上記の証明の最初にあるタクティクの状態を調べると，Leanが確かにすべての変数を取り込んでいることがわかります．宣言のスコープは ``section ... end`` ブロックに入れることで区切ることができます．最後に， introduction でご紹介した式の型を決定するコマンドを思い出してください：
TEXT. -/

-- QUOTE:
section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end
-- QUOTE.

/- OMIT:
The ``#check`` command works for both objects and facts.
In response to the command ``#check a``, Lean reports that ``a`` has type ``ℝ``.
In response to the command ``#check mul_comm a b``,
Lean reports that ``mul_comm a b`` is a proof of the fact ``a * b = b * a``.
The command ``#check (a : ℝ)`` states our expectation that the
type of ``a`` is ``ℝ``,
and Lean will raise an error if that is not the case.
We will explain the output of the last three ``#check`` commands later,
but in the meanwhile, you can take a look at them,
and experiment with some ``#check`` commands of your own.

Let's try some more examples. The theorem ``two_mul a`` says
that ``2 * a = a + a``. The theorems ``add_mul`` and ``mul_add``
express the distributivity of multiplication over addition,
and the theorem ``add_assoc`` expresses the associativity of addition.
Use the ``#check`` command to see the precise statements.

.. index:: calc, tactics ; calc
OMIT. -/

/- TEXT:
checkコマンドはモノとコトの両方に使用することができます．``#check a`` を実行すると，Lean は ``a`` が ``ℝ`` 型であることを報告します．``#check mul_comm a b`` を実行すると，Lean は ``mul_comm a b`` が ``a * b = b * a`` という事実の証明であることを報告します．``#check (a : ℝ)`` は ``a`` の型が ``ℝ`` であることを確認するもので，もしそうでなければエラーになります．最後の3つの ``#check`` コマンドの出力については後ほど説明します．それまで自由に上記のコマンド例を確認したり， 自分で ``#check`` コマンドを試したりしてみてください．
もう少し例を挙げてみましょう．定理 ``two_mul a`` は ``2 * a = a + a`` を表しています．定理 ``add_mul`` と ``mul_add`` は足し算に対する掛け算の分配性を表し，定理 ``add_assoc`` は足し算の結合則を表しています．正確な記述を見るには ``#check`` コマンドを使ってください．

.. index:: calc, tactics ; calc
TEXT. -/

section
variable (a b : ℝ)

-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]
-- QUOTE.

/- OMIT:
Whereas it is possible to figure out what it going on in this proof
by stepping through it in the editor,
it is hard to read on its own.
Lean provides a more structured way of writing proofs like this
using the ``calc`` keyword.
OMIT. -/

/- TEXT:
この証明で何が起こっているのかをエディター上で読み進めて理解することもできなくはないですが，これだけでは読みにくいことでしょう．Leanでは ``calc`` というキーワードを使用して,このような証明をより構造的に書くことができます．
TEXT. -/

-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
-- QUOTE.

/- OMIT:
Notice that the proof does *not* begin with ``by``:
an expression that begins with ``calc`` is a *proof term*.
A ``calc`` expression can also be used inside a tactic proof,
but Lean interprets it as the instruction to use the resulting
proof term to solve the goal.
The ``calc`` syntax is finicky: the underscores and justification
have to be in the format indicated above.
Lean uses indentation to determine things like where a block
of tactics or a ``calc`` block begins and ends;
try changing the indentation in the proof above to see what happens.

One way to write a ``calc`` proof is to outline it first
using the ``sorry`` tactic for justification,
make sure Lean accepts the expression modulo these,
and then justify the individual steps using tactics.
OMIT. -/

/- TEXT:
この証明が ``by`` で始まっていないことに注意してください．``calc`` で始まる式は証明項です．``calc`` 式はタクティクスタイルの証明の中で使うこともできますが，Leanはそれを，結果として得られる証明項を使ってゴールを証明するという指示として解釈します．``calc`` の構文は制約の多いものです．下線と空白の入れ方は上記の形式でなければなりません．インデントを使って，タクティクのブロックや ``calc`` ブロックの始まりと終わりを決定しています．上の証明のインデントを変えてみてどうなるか見てみましょう．
``calc`` による証明の書き方の一例として，まず各式変形の証明を ``sorry`` タクティクで置いて式変形の概要を書き，これをLeanが受け入れることを確認してから ``sorry`` としていた各式変形をタクティクで証明していく，というものがあります．
TEXT. -/

-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry
-- QUOTE.

end

/- OMIT:
Try proving the following identity using both a pure ``rw`` proof
and a more structured ``calc`` proof:
OMIT. -/

/- TEXT:
純粋な ``rw`` による証明と，より構造化された ``calc`` による証明の両方を使用して，以下の等式を証明してください.
TEXT. -/


-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

-- QUOTE:
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry
-- QUOTE.

/- OMIT:
The following exercise is a little more challenging.
You can use the theorems listed underneath.
OMIT. -/

/- TEXT:
この後の演習は少し難しいです．下に挙げた定理を使用すると良いでしょう．
TEXT. -/

-- QUOTE:
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
-- QUOTE.

end

/- OMIT:
.. index:: rw, tactics ; rw and rewrite

We can also perform rewriting in an assumption in the context.
For example, ``rw [mul_comm a b] at hyp`` replaces ``a * b`` by ``b * a``
in the assumption ``hyp``.
OMIT. -/

/- TEXT:
.. index:: rw, tactics ; rw and rewrite

また，コンテキストにある仮定に対して書き換えを行うことも可能です．例えば， ``rw [mul_comm a b] at hyp`` は ``hyp`` という仮定の中の ``a * b`` を ``b * a`` に置き換えます．
TEXT. -/

-- Examples.

section
variable (a b c d : ℝ)

-- QUOTE:
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp
-- QUOTE.

/- OMIT:
.. index:: exact, tactics ; exact

In the last step, the ``exact`` tactic can use ``hyp`` to solve the goal
because at that point ``hyp`` matches the goal exactly.

.. index:: ring (tactic), tactics ; ring

We close this section by noting that Mathlib provides a
useful bit of automation with a ``ring`` tactic,
which is designed to prove identities in any commutative ring as long as they follow
purely from the ring axioms, without using any local assumption.
OMIT. -/

/- TEXT:
.. index:: exact, tactics ; exact

最後のステップで ``exact`` タクティクで ``hyp`` を使ってゴールを達成することができます．なぜなら，その時点で ``hyp`` はゴールと完全に一致するからです．

.. index:: ring (tactic), tactics ; ring

このセクションの最後に，Mathlibが ``ring`` タクティクという便利なオートメーションを提供していることに触れておきます．ring は，ローカルの仮定を用いずに純粋に環の公理だけから導かれるような，任意の可換環における恒等式を証明できるように設計されています．
TEXT. -/

-- QUOTE:
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
-- QUOTE.

end

/- OMIT:
The ``ring`` tactic is imported indirectly when we
import ``Mathlib.Data.Real.Basic``,
but we will see in the next section that it can be used
for calculations on structures other than the real numbers.
It can be imported explicitly with the command
``import Mathlib.Tactic``.
We will see there are similar tactics for other common kind of algebraic
structures.

There is a variation of ``rw`` called ``nth_rw`` that allows you to replace only particular instances of an expression in the goal.
Possible matches are enumerated starting with 1,
so in the following example, ``nth_rw 2 [h]`` replaces the second
occurrence of ``a + b`` with ``c``.
OMIT. -/

/- TEXT:
``ring`` タクティクは ``Mathlib.Data.Real.Basic`` をインポートしたときに間接的にインポートされています．しかし，次章では実数以外の構造体の計算にも ``ring`` タクティクが使用できることを解説していきます． ``ring`` は ``import Mathlib.Tactic`` コマンドを使用して明示的にインポートすることができます．他の代数的対象にも同様のタクティクがあることを今後見ていきます． ``nth_rw`` と呼ばれる ``rw`` の亜種が存在し，それを使用するとゴール(証明したい命題)の中にある表現のうち特定のものだけを置換することができます．ありうる置換対象は1から順番に列挙されます．次の例では ``nth_rw 2 h`` は2番目に出現する ``a + b`` を ``c`` に置換しています．

EXAMPLES: -/
-- QUOTE:
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
-- QUOTE.
