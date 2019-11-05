$(
	Level 1: ML Syntax Primitives
$)

$c \bot $.    $( the bottom pattern $)
$c \imp $.    $( the implication pattern ( \imp P Q ) $)
$c \app $.    $( the application pattern ( \app P Q ) $)
$c \exists $. $( the exists quantifier ( \exists x P ) $)
$c \mu $.     $( the mu fixpoint binder ( \mu X P ) $)
$c ( $.       $( left parenthesis $)
$c ) $.       $( right parenthesis $)

$c #wf $.     $( wellformedness token $)
$c #var $.    $( variable token $)
$c #symb $.   $( symbols token $)
$c #evar $.   $( element variables token $)
$c #svar $.   $( set variables token $)

$c |- $.      $( the provability token $)

$( Declare metamath variables and their ranges. $)

$v 
	P Q R P' Q' R' 
    x y z 
    X Y Z 
    f g h 
    xX yY
$.

wfP   $f #wf P $.
wfQ   $f #wf Q $.
wfR   $f #wf R $.
wfPp  $f #wf P' $.
wfQp  $f #wf Q' $.
wfRp  $f #wf R' $.

evarx $f #evar x $.
evary $f #evar y $.
evarz $f #evar z $.

svarX $f #svar X $.
svarY $f #svar Y $.
svarZ $f #svar Z $.

symbf $f #symb f $.
symbg $f #symb g $.
symbh $f #symb h $.

varxX $f #var xX $.
varyY $f #var yY $.

$( State that element/set variables are variables. $)

var-evar $a #var x $.
var-svar $a #var X $.

$( auxiliary tokens $)

$c #nnegative $. $( non-negative occurrence token; 
                  ( #nnegative X P ) means X does not occur negatively in P. $)
				  
$c #npositive $. $( non-positive occurrence token; 
                  ( #npositive X P ) means X does not occur positively in P. $)

$c #nfree $.     $( not-occur-free token;
                  ( #nfree xX P ) means xX does not occur 
				  free in P. $)
                          
$c #appctx $.    $( application context token;
                  ( #appctx P xX ) means P is an application context wrt variable xX. $)

$( Define wellformedness token #wf. $)

wf-var    $a #wf xX $. 
wf-bot    $a #wf \bot $.
wf-imp    $a #wf ( \imp P Q ) $.
wf-app    $a #wf ( \app P Q ) $.
wf-exists $a #wf ( \exists x P ) $.
${
    wf-mu.1 $e #nnegative X P $.
    wf-mu   $a #wf ( \mu X P ) $.
$}

$( Define non-negative occurrence token ( #nnegative X P ). $)

nnegative-var  $a #nnegative X xX $.
nnegative-symb $a #nnegative X f $.
nnegative-bot  $a #nnegative X \bot $.
${
    nnegative-imp.1 $e #npositive X P $.
    nnegative-imp.2 $e #nnegative X Q $.
    nnegative-imp   $a #nnegative X ( \imp P Q ) $.
$}
${
    nnegative-app.1 $e #nnegative X P $.
    nnegative-app.2 $e #nnegative X Q $.
    nnegative-app   $a #nnegative X ( \app P Q ) $.
$}
${
   nnegative-exists.1 $e #nnegative X P $.
   nnegative-exists   $a #nnegative X ( \exists x P ) $.
$}
nnegative-mu-binding $a #nnegative X ( \mu X P ) $.
${
    $d X Y $.
    nnegative-mu-body.1 $e #nnegative X P $.
    nnegative-mu-body   $a #nnegative X ( \mu Y P ) $.
$}

$( Define non-positive occurrence token ( #npositive X P ). $)

${
    $d X xX $.
    npositive-var  $a #npositive X xX $.
$}
npositive-symb $a #npositive X f $.
npositive-bot  $a #npositive X \bot $.
${
    npositive-imp.1 $e #nnegative X P $.
    npositive-imp.2 $e #npositive X Q $.
    npositive-imp   $a #npositive X ( \imp P Q ) $.
$}
${
    npositive-app.1 $e #npositive X P $.
    npositive-app.2 $e #npositive X Q $.
    npositive-app   $a #npositive X ( \app P Q ) $.
$}
${
   npositive-exists.1 $e #npositive X P $.
   npositive-exists   $a #npositive X ( \exists x P ) $.
$}
npositive-mu-binding $a #npositive X ( \mu X P ) $.
${
    $d X Y $.
    npositive-mu-body.1 $e #npositive X P $.
    npositive-mu-body   $a #npositive X ( \mu Y P ) $.
$}

$( Prove that element/set variables are wellformed. $)

wf-evar $p #wf x $= 
  evarx var-evar wf-var $.
wf-svar $p #wf X $=
  svarX var-svar wf-var $.

$( Define #nfree token ( #nfree xX P ). $)

${
    $d xX yY $.
    nfree-var $a #nfree xX yY $.
$}
nfree-symb $a #nfree xX f $.
nfree-bot  $a #nfree xX \bot $.
${
    nfree-imp.1 $e #nfree xX P $.
    nfree-imp.2 $e #nfree xX Q $.
    nfree-imp   $a #nfree xX ( \imp P Q ) $.
$}
${
    nfree-app.1 $e #nfree xX P $.
    nfree-app.2 $e #nfree xX Q $.
    nfree-app   $a #nfree xX ( \app P Q ) $.
$}
nfree-exists-binding $a #nfree x ( \exists x P ) $.
${
    $d xX y $.
    nfree-exists-body.1 $e #nfree xX P $.
    nfree-exists-body   $a #nfree xX ( \exists y P ) $.
$}
nfree-mu-binding $a #nfree X ( \mu X P ) $.
${
    $d xX Y $.
    nfree-mu-body.1 $e #nfree xX P $.
    nfree-mu-body   $a #nfree xX ( \exists Y P ) $.
$}

$( Define appliation context token ( #appctx P xX ). $)

appctx-var $a #appctx xX xX $.
${
    appctx-app-left.1 $e #appctx P xX $.
    appctx-app-left.2 $e #nfree xX Q $.
    appctx-app-left   $a #appctx ( \app P Q ) xX $.
$}
${
    appctx-app-right.1 $e #appctx Q xX $.
    appctx-app-right.2 $e #nfree xX P $.
    appctx-app-right   $a #appctx ( \app P Q ) xX $.
$}

$(
	Level 2: ML Metalevel Extension
$)

$c #eqq $. $( the metalevel equality ( #eqq P Q ) $)

eqq-self $a #eqq P P $.
${
    eqq-imp.1 $e #eqq P Q $.
    eqq-imp.2 $e #eqq P' Q' $.
    eqq-imp   $a #eqq ( \imp P P' ) ( \imp Q Q' ) $.
$}
${
    eqq-app.1 $e #eqq P Q $.
    eqq-app.2 $e #eqq P' Q' $.
    eqq-app   $a #eqq ( \app P P' ) ( \app Q Q' ) $.
$}
${
    eqq-exists.1 $e #eqq P Q $.
    eqq-exists   $a #eqq ( \exists x P ) ( \exists x Q ) $.
$}
${
    eqq-mu.1 $e #eqq P Q $.
    eqq-mu   $a #eqq ( \mu X P ) ( \mu X Q ) $.
$}

${
    eqq-nfree.1 $e #nfree yY Q $.
    eqq-nfree.2 $e #eqq xX yY $.
    eqq-nfree.3 $e #eqq P Q $.
    eqq-nfree   $a #nfree xX P $.
$}

${
    eqq-subst.1 $e #subst P' Q' R' xX $.
    eqq-subst.2 $e #eqq P P' $.
    eqq-subst.3 $e #eqq Q Q' $.
    eqq-subst.4 $e #eqq R R' $.
    eqq-subst.5 $e #eqq yY xX $.
    eqq-subst $a #subst P Q R yY $.
$}

${
    eqq-nnegative.1 $e #nnegative Y Q $.
    eqq-nnegative.2 $e #eqq X Y $.
    eqq-nnegative.3 $e #eqq P Q $.
    eqq-nnegative   $a #nnegative X P $.
$}

${
    eqq-npositive.1 $e #npositive Y Q $.
    eqq-npositive.2 $e #eqq X Y $.
    eqq-npositive.3 $e #eqq P Q $.
    eqq-npositive   $a #npositive X P $.
$}

${
    eqq-appctx.1 $e #appctx y Q $.
    eqq-appctx.2 $e #eqq x y $.
    eqq-appctx.3 $e #eqq P Q $.
    eqq-appctx   $a #appctx x P $.
$}

${
    eqq-thm.1 $e |- Q $.
    eqq-thm.2 $e #eqq P Q $.
    eqq-thm   $a |- P $.
$}

$c #subst $.     $( capture-avoiding substitution token; 
				  ( #subst P Q R xX ) means P is the result of
                  substituting R for xX in Q. $)

$( 
    Define capture-avoiding substitution "subst P Q R xx",
    meaning that P is the result of substituting R for xX in Q.
    Note that xX can be either element variable or set variable.
$)

subst-var-same $a #subst R xX R xX $.

${
    $d xX yY $.
    subst-var-diff $a #subst yY yY R xX $.
$}

subst-symb  $a #subst f f R xX $.
subst-bot $a #subst \bot \bot R xX $.

${
    subst-imp.1 $e #subst P  Q  R xX $.
    subst-imp.2 $e #subst P' Q' R xX $.
    subst-imp   $a #subst ( \imp P P' ) ( \imp Q Q' ) R xX $.
$}

${
    subst-app.1 $e #subst P  Q  R xX $.
    subst-app.2 $e #subst P' Q' R xX $.
    subst-app   $a #subst ( \app P P' ) ( \app Q Q' ) R xX $.
$}

subst-exists-binding $a #subst ( \exists x Q ) ( \exists x Q ) R x $.

${
    $d y xX z $.
    subst-exists-body.1 $e #subst Q P z y $.
    subst-exists-body.2 $e #subst Q' Q R xX $.
    subst-exists-body   $a #subst ( \exists z Q' ) ( \exists y P ) R xX $.
$}

subst-mu-binding $a #subst ( \mu X P ) ( \mu X P ) R X $.

${
    $d Y xX Z $.
    subst-mu-body.1 $e #subst Q P Z Y $.
    subst-mu-body.2 $e #subst Q' Q R xX $.
    subst-mu-body   $a #subst ( \mu Z Q' ) ( \mu Y P ) R xX $.
$}


$( Define propositional logic $)

rl-1 $a |- ( \imp P ( \imp Q P ) ) $.

rl-2 $a |- ( \imp ( \imp P ( \imp Q R ) )
                  ( \imp ( \imp P Q ) ( \imp P R ) ) ) $.
                   
rl-3 $a |- ( \imp ( \imp ( \imp P \bot ) \bot ) P ) $.

${
    rl-mp.1   $e |- P $.
    rl-mp.2   $e |- ( \imp P Q ) $.
    rl-mp     $a |- Q $.
$}

$( 
    Our first theorem, "id".
$)

id $p |- ( \imp P P ) $=
  wfP wfP wfP wf-imp wf-imp wfP wfP wf-imp wfP wfP rl-1 wfP wfP wfP
  wf-imp wfP wf-imp wf-imp wfP wfP wfP wf-imp wf-imp wfP wfP wf-imp wf-imp wfP wfP wfP
  wf-imp rl-1 wfP wfP wfP wf-imp wfP rl-2 rl-mp
  rl-mp $.

$(
	\iff is a derived construct that can be defined from \imp and \bot. 
	For now, we add it here as a builtin.
$)
$c \iff $.
wf-iff $a #wf ( \iff P Q ) $.
${
    iff-intro.1 $e |- ( \imp P Q ) $.
	iff-intro.2 $e |- ( \imp Q P ) $.
	iff-intro   $a |- ( \iff P Q ) $.
$}
${
	iff-elim-fw.1 $e |- ( \iff P Q ) $.
	iff-elim-fw   $a |- ( \imp P Q ) $.
$}
${
	iff-elim-bw.1 $e |- ( \iff P Q ) $.
	iff-elim-bw   $a |- ( \imp Q P ) $.
$}

$(
	\iff yields a congruence relation in terms of provability.
$)
${
	iff-thm.1 $e |- ( \iff P Q ) $.
	iff-thm.2 $e |- P $.
	iff-thm   $p |- Q $=
  wfP wfQ iff-thm.2 wfP wfQ iff-thm.1 iff-elim-fw rl-mp $.
$}









$(  THIS DOESN'T WORK: P Q must be #wf already.
    eqq-wf.1 $e #wf Q $.
    eqq-wf.2 $e #eqq P Q $.
    eqq-wf   $a #wf P $.
$)

$(  DON'T NEED THESE RIGHT NOW.
    eqq-var.1 $e #var yY $.
    eqq-var.2 $e #eqq xX yY $.
    eqq-var   $a #var xX $.
$)

$(  DON'T NEED THESE RIGHT NOW.
    eqq-evar.1 $e ev y $.
    eqq-evar.2 $e #eqq x y $.
    eqq-evar   $a ev x $.
$)

$(  DON'T NEED THESE RIGHT NOW. 
    eqq-svar.1 $e sv Y $.
    eqq-svar.2 $e #eqq X Y $.
    eqq-svar   $a sv X $.
$)

$(  DON'T NEED THESE RIGHT NOW. 
    eqq-symb.1 $e #symb g $.
    eqq-symb.2 $e #eqq f g $.
    eqq-symb   $a #symb f $.
$)



$(
    State AML proof rules (rl).
$)

$(
    AML proof rules Part B: FOL reasoning.
$)

${
    rl-exists-inst.1 $e #subst P Q y x $.
    rl-exists-inst   $a |- ( \imp P ( \exists x Q ) ) $.
$}

${
    rl-exists-gen.1 $e |- ( \imp P Q ) $.
    rl-exists-gen.2 $e #nfree x P $.
    rl-exists-gen   $a |- ( \imp P ( \exists x Q ) ) $.
$}

$(
    AML proof rules Part C: Frame reasoning.
$)

rl-propagation-bot-left  $a |- ( \imp ( \app \bot P ) \bot ) $.
rl-propagation-bot-right $a |- ( \imp ( \app P \bot ) \bot ) $.
rl-propagation-or-left 
  $a |- ( \imp ( \app ( \imp ( \imp P \bot ) Q ) R )
               ( \imp ( \imp ( \app P R ) \bot ) ( \app Q R ) ) ) $.
rl-propagation-or-right 
  $a |- ( \imp ( \app R ( \imp ( \imp P \bot ) Q ) )
               ( \imp ( \imp ( \app R P ) \bot ) ( \app R Q ) ) ) $.
${
    rl-propagation-exists-left.1
      $e #nfree x Q $.
    rl-propagation-exists-left
      $a |- ( \imp ( \app ( \exists x P ) Q )
                   ( \exists x ( \app P Q ) ) ) $.
$}

${
    rl-propagation-exists-right.1
      $e #nfree x Q $.
    rl-propagation-exists-right
      $a |- ( \imp ( \app Q ( \exists x P ) )
                   ( \exists x ( \app Q P ) ) ) $.
$}

${
    rl-framing-left.1 $e |- ( \imp P Q ) $.
    rl-framing-left   $a |- ( \imp ( \app P R ) ( \app Q R ) ) $.
$}

${
    rl-framing-right.1 $e |- ( \imp P Q ) $.
    rl-framing-right   $a |- ( \imp ( \app R P ) ( \app R Q ) ) $.
$}

$(
    AML proof rules Part D: Fixpoint reasoning.
$)

${
    rl-svar-subst.1 $e |- Q $.
    rl-svar-subst.2 $e #subst P Q R Y $.
    rl-svar-subst $a |- P $.
$}

${
    rl-prefixpoint.1 $e #subst Q P ( \mu X P ) X $.
    rl-prefixpoint   $a |- ( \imp Q ( \mu X P ) ) $.
$}

${
    rl-kt.1 $e |- ( \imp R Q ) $.
    rl-kt.2 $e #subst R P Q X $.
    rl-kt   $a |- ( \imp ( \mu X P ) Q ) $.
$}

$(
    AML proof rules Part E: Misc technical proof rules.
$)

rl-existence $a |- ( \exists x x ) $.

${
    p2inf.1 $e |- ( \imp P ( \imp Q R ) ) $.
    p2inf   $p |- ( \imp ( \imp P Q ) ( \imp P R ) ) $=
      wfP wfQ wfR wf-imp wf-imp wfP wfQ wf-imp wfP wfR wf-imp wf-imp p2inf.1 wfP
      wfQ wfR rl-2 rl-mp $.
$}

$(
    Singelton Variables.
$)

${
    nflipb $p |- ( \imp ( \imp ( \imp P \bot ) ( \imp Q \bot ) ) ( \imp Q P ) ) $= ? $.
$}

$( 
    Our first definition: negation.
    ( \neg P ) === ( \imp P \bot ) 
$)

$c \neg $.
wf-neg $a #wf ( \neg P ) $.
df-neg $a #eqq ( \neg P ) ( \imp P \bot ) $.

$( 
    Prove metalevel properties about negations.
$)

${
    nfree-neg.1 $e #nfree xX P $.
    nfree-neg   $p #nfree xX ( \neg P ) $=
  wfP wf-neg wfP wf-bot wf-imp varxX varxX wfP wf-bot varxX nfree-neg.1 varxX
  nfree-bot nfree-imp varxX wf-var eqq-self wfP df-neg eqq-nfree $.
$}

${
    subst-neg.1 $e #subst P' P R yY $.
    subst-neg   $p #subst ( \neg P' ) ( \neg P ) R yY $=
      wfPp wf-neg wfP wf-neg wfR wfPp wf-bot wf-imp wfP wf-bot wf-imp wfR varyY varyY
      wfPp wfP wfR wf-bot wf-bot varyY subst-neg.1 wfR varyY subst-bot subst-imp
      wfPp df-neg wfP df-neg wfR eqq-self varyY wf-var eqq-self eqq-subst $.
$}

${
    nnegative-neg.1 $e #npositive X P $.
    nnegative-neg   $p #nnegative X ( \neg P ) $=
      wfP wf-neg wfP wf-bot wf-imp svarX svarX wfP wf-bot svarX nnegative-neg.1 
      svarX nnegative-bot nnegative-imp svarX wf-svar eqq-self wfP df-neg 
      eqq-nnegative $.
$}

${
    npositive-neg.1 $e #nnegative X P $.
    npositive-neg   $p #npositive X ( \neg P ) $=
      wfP wf-neg wfP wf-bot wf-imp svarX svarX wfP wf-bot svarX npositive-neg.1 
      svarX npositive-bot npositive-imp svarX wf-svar eqq-self wfP df-neg 
      eqq-npositive $.
$}

$( 
    Prove some metatheorems about negations. 
$)

${
    nn $p |- ( \imp ( \neg ( \neg P ) ) P ) $=
      wfP wf-neg wf-neg wfP wf-imp wfP wf-neg wf-bot wf-imp wfP wf-imp wfP wf-neg wf-bot
      wf-imp wfP wf-imp wfP wf-bot wf-imp wf-bot wf-imp wfP wf-imp wfP
      rl-3 wfP wf-neg wf-bot wf-imp wfP wf-bot wf-imp wf-bot wf-imp wfP
      wfP wfP wf-neg wfP wf-bot wf-imp wf-bot wf-bot wfP df-neg wf-bot eqq-self
      eqq-imp wfP eqq-self eqq-imp eqq-thm wfP wf-neg wf-neg wfP wf-neg wf-bot
      wf-imp wfP wfP wfP wf-neg df-neg wfP eqq-self eqq-imp eqq-thm $.
$}

${
    nflip $p |- ( \imp ( \imp ( \neg P ) ( \neg Q ) ) ( \imp Q P ) ) $=
      wfP wf-neg wfQ wf-neg wf-imp wfQ wfP wf-imp wf-imp wfP wf-bot wf-imp wfQ wf-bot
      wf-imp wf-imp wfQ wfP wf-imp wf-imp wfP wfQ nflipb wfP wf-neg wfQ wf-neg wf-imp
      wfP wf-bot wf-imp wfQ wf-bot wf-imp wf-imp wfQ wfP wf-imp wfQ wfP wf-imp wfP
      wf-neg wfP wf-bot wf-imp wfQ wf-neg wfQ wf-bot wf-imp wfP df-neg wfQ df-neg
      eqq-imp wfQ wfP wf-imp eqq-self eqq-imp eqq-thm $.
$}



$(
    Defind \forall x P === \neg ( \exists x ( \neg P ) )
$)

$c \forall $.
wfforall $a \forall x P $.
df-forall $a #eqq ( \forall x P ) ( \neg ( \exists x ( \neg P ) ) ) $.

$c \app2 $.
wf-app2 $a #wf ( \app2 P Q R ) $.
df-app2 $a #eqq ( \app2 P Q R ) ( \app ( \app P Q ) R ) $.

$c \eq $.
wf-eq $a #wf ( \eq P Q ) $.
${
	eq-thm.1 $e |- ( \eq P Q ) $.
	eq-thm.2 $e |- Q $.
	eq-thm   $a |- P $.
$}

$( SIMP Definitions $)

$(

module SIMP
  syntax State ::= pair(Int,Int)
  rule pair(X,Y) => pair(X-1,Y+X) requires X >=Int 1
endmodule

$)

$( Define all K sorts. $)

$c Int Id KResult K List Map $.

$c Exp Stmt Pgm Ids $.

$c KCell StateCell TopCell k state t $.

$( int n, s; n = 1; while(n){s=s+n; n=n-1} $)

$c plusExp minusExp seqStmt ifStmt whileStmt assignStmt decvarPgm n s $.

$c SUM1 WHILE BODY ASSIGN-S ASSIGN-N  $.

symbInt $a #symb Int $.
symbId $a #symb Id $.
symbKResult $a #symb KResult $.
symbK $a #symb K $.
symbList $a #symb List $.
symbMap $a #symb Map $.

$( Some definitions about integers and maps $)
$c zero succ $. $( natural number constructors $)
symbzero $a #symb zero $.
symbsucc $a #symb succ $.

$c 0 1 2 3 4 5 $. $( literal values $)
symb0 $a #symb 0 $.
symb1 $a #symb 1 $.
symb2 $a #symb 2 $.
symb3 $a #symb 3 $.
symb4 $a #symb 4 $.
symb5 $a #symb 5 $.

df-0 $a #eqq 0 zero $.
df-1 $a #eqq 1 ( \app succ 0 ) $.
df-2 $a #eqq 2 ( \app succ 1 ) $.
df-3 $a #eqq 3 ( \app succ 2 ) $.
df-4 $a #eqq 4 ( \app succ 3 ) $.
df-5 $a #eqq 5 ( \app succ 4 ) $.

$c nil cons $. $( cons-lists constructors $)
symbnil $a #symb nil $.
symbcons $a #symb cons $.

$c list1 list2 $.
symblist1 $a #symb list1 $.
symblist2 $a #symb list2 $.
df-list1 $a |- ( \eq ( \app list1 P ) ( \app2 cons P nil ) ) $.
df-list2 $a |- ( \eq ( \app2 list2 P Q ) ( \app2 cons P ( \app list1 P ) ) ) $.

$c map2 mapsto $.
 
symbExp $a #symb Exp $.
symbStmt $a #symb Stmt $.
symbPgm $a #symb Pgm $.
symbIds $a #symb Ids $.
 
symbKCell $a #symb KCell $.
symbStateCell $a #symb StateCell $.
symbTopCell $a #symb TopCell $.
symbk $a #symb k $.
symbstate $a #symb state $.
symbt $a #symb t $.
 
symbplusExp $a #symb plusExp $.
symbminusExp $a #symb minusExp $.
symbseqStmt $a #symb seqStmt $.
symbifStmt $a #symb ifStmt $.
symbwhileStmt $a #symb whileStmt $.
symbassignStmt $a #symb assignStmt $.
symbdecvarPgm $a #symb decvarPgm $.
symbn $a #symb n $.
symbs $a #symb s $.

symbSUM1 $a #symb SUM1 $.
symbWHILE $a #symb WHILE $.
symbBODY $a #symb BODY $.
symbASSIGN-S $a #symb ASSIGN-S $.
symbASSIGN-N $a #symb ASSIGN-N $.

df-ASSIGN-S $a #eqq ASSIGN-S ( \app2 assignStmt s ( \app2 plusExp  s n ) ) $.
df-ASSIGN-N $a #eqq ASSIGN-N ( \app2 assignStmt n ( \app2 minusExp n 1 ) ) $.
df-BODY $a #eqq BODY ( \app2 seqStmt ASSIGN-S ASSIGN-N ) $.
df-WHILE $a #eqq WHILE ( \app2 whileStmt n  BODY ) $.
df-SUM1 $a #eqq SUM1 ( \app2 decvarPgm ( \app2 list2 n s ) ( \app2 seqStmt ( \app2 assignStmt n 1 ) WHILE ) ) $.

$( Representing SUM configurations: code, value of n, value of s $)

$c \cfg $.
wf-cfg $a #wf ( \cfg P Q R ) $.
df-cfg $a #eqq ( \cfg P Q R ) 
               ( \app2 t ( \app k P ) ( \app state ( map2 ( \app2 mapsto n Q ) ( \app2 mapsto s R ) ) ) ) $.



