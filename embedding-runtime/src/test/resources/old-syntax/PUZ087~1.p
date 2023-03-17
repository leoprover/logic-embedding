%------------------------------------------------------------------------------
% File     : PUZ087~1 : TPTP v9.0.0. Released v9.0.0.
% Domain   : Puzzles
% Problem  : Wise men
% Version  : Especial.
% English  : Once upon a time, a king wanted to find the wisest out of his
%            three wisest men. He arranged them in a circle and told them that
%            he would put a white or a black spot on their foreheads and that
%            one of the three spots would certainly be white. The three wise
%            men could see and hear each other but, of course, they could not
%            see their faces reflected anywhere. The king, then, asked to each
%            of them to find out the colour of his own spot. After a while, the
%            wisest correctly answered that his spot was white.

% Refs     : [Gol92] Goldblatt (1992), Logics of Time and Computation
%          : [Bal98] Baldoni (1998), Normal Multimodal Logics: Automatic De
% Source   : [TPTP]
% Names    : 

% Status   : Theorem
% Rating   : ? v9.0.0
% Syntax   : TBA
% SPC      : TFN_THM_NEQ

% Comments : Long connectives
%------------------------------------------------------------------------------
tff(simple_s5,logic,(
    $epistemic_modal ==
        [ $constants == $rigid,
          $quantification == $varying,
          $consequence == $global,
          $modalities == $modal_system_S5 ] )).

%----Type for the wise men
tff(agent_type,type,wiseman: $tType).

%----Three wise men
tff(man_a_type,type,a: wiseman).

tff(man_b_type,type,b: wiseman).

tff(man_c_type,type,c: wiseman).

tff(fool_type,type,fool: wiseman).

%---Property of a wiseman's hat: white_spot
tff(white_spot_type,type,white_spot: wiseman > $o).

%----At least one wiseman has a white spot
tff(at_least_one_white_spot,axiom,(
    {$knows:#fool}((white_spot(a)) | (white_spot(b)) | (white_spot(c))) )).

%----If one agent has a white spot all other agents can see this
tff(b_knows_a,axiom,(
    {$knows:#fool}(
      ( white_spot(a)
     => {$knows:#b}(white_spot(a)) ) ) )).

tff(c_knows_a,axiom,(
    {$knows:#fool}(
      ( white_spot(a)
     => {$knows:#c}(white_spot(a)) ) ) )).

tff(a_knows_a,axiom,(
    {$knows:#fool}(
      ( white_spot(b) 
     => {$knows:#a}(white_spot(b)) ) ) )).

tff(c_knows_b,axiom,(
    {$knows:#fool}(
      ( white_spot(b) 
     => {$knows:#c}(white_spot(b)) ) ) )).

tff(a_knows_c,axiom,(
    {$knows:#fool}(
      ( white_spot(c) 
     => {$knows:#a}(white_spot(c)) ) ) )).

tff(b_knows_c,axiom,(
    {$knows:#fool}(
      ( white_spot(c) 
     => {$knows:#b}(white_spot(c)) ) ) )).

%----Black spots are visible
tff(b_knows_not_a,axiom,(
    {$knows:#fool}(
      ( ~ white_spot(a) 
     => {$knows:#b}(~ white_spot(a)) ) ) )).

tff(c_knows_not_a,axiom,(
    {$knows:#fool}( 
      ( ~ white_spot(a) 
     => {$knows:#c}(~ white_spot(a)) ) ) )).

tff(a_knows_not_b,axiom,(
    {$knows:#fool}( 
      ( ~ white_spot(b) 
     => {$knows:#a}(~ white_spot(b)) ) ) )).

tff(c_knows_not_b,axiom,(
    {$knows:#fool}( 
      ( ~ white_spot(b) 
     => {$knows:#c}(~ white_spot(b)) ) ) )).

tff(a_knows_not_c,axiom,(
    {$knows:#fool}( 
      ( ~ white_spot(c) 
     => {$knows:#a}(~ white_spot(c)) ) ) )).

tff(b_knows_not_c,axiom,(
    {$knows:#fool}( 
      ( ~ white_spot(c) 
     => {$knows:#b}(~ white_spot(c)) ) ) )).

%----a and b don't know their situation
tff(a_not_know,axiom,(
    {$knows:#fool}(~ {$knows:#a}(white_spot(a))) )).

tff(b_not_know,axiom,(
    {$knows:#fool}(~ {$knows:#b}(white_spot(b))) )).

%----Prove c knows white spot
tff(c_knows,conjecture,(
    {$knows:#c}(white_spot(c)) )).

%------------------------------------------------------------------------------
