%------------------------------------------------------------------------------
% File     : PUZ087#3 : TPTP v9.0.0. Released v9.0.0.
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
%          : [Ste21] Steen (2021), Email to Geoff Sutcliffe
% Source   : [Ste21]
% Names    : ex5_multimodal_wiseman.p [Ste21]

% Status   : Theorem
% Rating   : ? v9.0.0
% Syntax   : TBA
% SPC      : THN_THM_NEQ

% Comments : Short connectives
%------------------------------------------------------------------------------
thf(simple_s5,logic,(
    $modal ==
        [ $constants == $rigid,
          $quantification == $varying,
          $consequence == $global,
          $modalities == $modal_system_S5 ] )).

%----Type for the wise men
thf(agent_type,type,wiseman: $tType).

%----Three wise men
thf(man_a_type,type,a: wiseman).

thf(man_b_type,type,b: wiseman).

thf(man_c_type,type,c: wiseman).

thf(fool_type,type,fool: wiseman).

%---Property of a wiseman's hat: white_spot
thf(white_spot_type,type,white_spot: wiseman > $o).

%----At least one wiseman has a white spot
thf(at_least_one_white_spot,axiom,(
    [#index_fool] @ 
      ( (white_spot @ a)
      | (white_spot @ b)
      | (white_spot @ c) ) )).

%----If one agent has a white spot all other agents can see this
thf(b_knows_a,axiom,(
    [#index_fool] @ 
      ( (white_spot @ a)
     => ( [#index_b] @ (white_spot @ a) ) ) )).

thf(c_knows_a,axiom,(
    [#index_fool] @ 
      ( (white_spot @ a)
     => ( [#index_c] @ (white_spot @ a) ) ) )).

thf(a_knows_a,axiom,(
    [#index_fool] @ 
      ( (white_spot @ b)
     => ( [#index_a] @ (white_spot @ b) ) ) )).

thf(c_knows_b,axiom,(
    [#index_fool] @ 
      ( (white_spot @ b)
     => ( [#index_c] @ (white_spot @ b) ) ) )).

thf(a_knows_c,axiom,(
    [#index_fool] @ 
      ( (white_spot @ c)
     => ( [#index_a] @ (white_spot @ c) ) ) )).

thf(b_knows_c,axiom,(
    [#index_fool] @ 
      ( (white_spot @ c)
     => ( [#index_b] @ (white_spot @ c) ) ) )).

%----Black spots are visible
thf(b_knows_not_a,axiom,(
    [#index_fool] @ 
      ( ~ (white_spot @ a)
     => ( [#index_b] @ ( ~ (white_spot @ a) ) ) ) )).

thf(c_knows_not_a,axiom,(
    [#index_fool] @ 
      ( ~ (white_spot @ a)
     => ( [#index_c] @ ( ~ (white_spot @ a) ) ) ) )).

thf(a_knows_not_b,axiom,(
    [#index_fool] @ 
      ( ~ (white_spot @ b)
     => ( [#index_a] @ ( ~ (white_spot @ b) ) ) ) )).

thf(c_knows_not_b,axiom,(
    [#index_fool] @ 
      ( ~ (white_spot @ b)
     => ( [#index_c] @ ( ~ (white_spot @ b) ) ) ) )).

thf(a_knows_not_c,axiom,(
    [#index_fool] @ 
      ( ~ (white_spot @ c)
     => ( [#index_a] @ ( ~ (white_spot @ c) ) ) ) )).

thf(b_knows_not_c,axiom,(
    [#index_fool] @ 
      ( ~ (white_spot @ c)
     => ( [#index_b] @ ( ~ (white_spot @ c) ) ) ) )).

%----a and b don't know their situation
thf(a_not_know,axiom,(
    [#index_fool] @ ( ~ ( [#index_a] @ (white_spot @ a) ) ) )).

thf(b_not_know,axiom,(
    [#index_fool] @ ( ~ ( [#index_b] @ (white_spot @ b) ) ) )).

%----Prove c knows white spot
thf(c_knows,conjecture,(
    [#index_c] @ (white_spot @ c) )).

%------------------------------------------------------------------------------
