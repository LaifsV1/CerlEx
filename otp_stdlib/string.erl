%%
%% Derived from Erlang/OTP's string.erl for CerlEx (2026): only the classic
%% character-list functions are kept, adapted to pure list code.
%%
%% Copyright Ericsson AB 1996-2023. All Rights Reserved.
%%
%% Licensed under the Apache License, Version 2.0 (the "License");
%% you may not use this file except in compliance with the License.
%% You may obtain a copy of the License at
%%
%%     http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing, software
%% distributed under the License is distributed on an "AS IS" BASIS,
%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%% See the License for the specific language governing permissions and
%% limitations under the License.
%%
-module(string).

-export([is_empty/1,
         len/1, concat/2,
         chr/2, rchr/2,
         str/2, rstr/2,
         span/2, cspan/2,
         substr/2, substr/3,
         tokens/2,
         chars/2, chars/3,
         copies/2,
         words/1, words/2,
         sub_word/2, sub_word/3,
         strip/1, strip/2, strip/3,
         left/2, left/3,
         right/2, right/3,
         centre/2, centre/3,
         sub_string/2, sub_string/3,
         to_lower/1, to_upper/1,
         join/2]).

-import(lists, [member/2]).

is_empty([]) -> true;
is_empty([_|_]) -> false.

len(S) -> erlang:length(S).

concat(S1, S2) -> S1 ++ S2.

chr(S, C) when is_integer(C) -> chr(S, C, 1).

chr([C|_Cs], C, I) -> I;
chr([_|Cs], C, I) -> chr(Cs, C, I+1);
chr([], _C, _I) -> 0.

rchr(S, C) when is_integer(C) -> rchr(S, C, 1, 0).

rchr([C|Cs], C, I, _L) ->
    rchr(Cs, C, I+1, I);
rchr([_|Cs], C, I, L) ->
    rchr(Cs, C, I+1, L);
rchr([], _C, _I, L) -> L.

str(S, Sub) when is_list(Sub) -> str(S, Sub, 1).

str([C|S], [C|Sub], I) ->
    case l_prefix(Sub, S) of
        true -> I;
        false -> str(S, [C|Sub], I+1)
    end;
str([_|S], Sub, I) -> str(S, Sub, I+1);
str([], _Sub, _I) -> 0.

rstr(S, Sub) when is_list(Sub) -> rstr(S, Sub, 1, 0).

rstr([C|S], [C|Sub], I, L) ->
    case l_prefix(Sub, S) of
        true -> rstr(S, [C|Sub], I+1, I);
        false -> rstr(S, [C|Sub], I+1, L)
    end;
rstr([_|S], Sub, I, L) -> rstr(S, Sub, I+1, L);
rstr([], _Sub, _I, L) -> L.

l_prefix([C|Pre], [C|String]) -> l_prefix(Pre, String);
l_prefix([], String) when is_list(String) -> true;
l_prefix(Pre, String) when is_list(Pre), is_list(String) -> false.

span(S, Cs) when is_list(Cs) -> span(S, Cs, 0).

span([C|S], Cs, I) ->
    case member(C, Cs) of
        true -> span(S, Cs, I+1);
        false -> I
    end;
span([], _Cs, I) -> I.

cspan(S, Cs) when is_list(Cs) -> cspan(S, Cs, 0).

cspan([C|S], Cs, I) ->
    case member(C, Cs) of
        true -> I;
        false -> cspan(S, Cs, I+1)
    end;
cspan([], _Cs, I) -> I.

substr(String, 1) when is_list(String) ->
    String;
substr(String, S) when is_integer(S), S > 1 ->
    substr2(String, S).

substr(String, S, L) when is_integer(S), S >= 1, is_integer(L), L >= 0 ->
    substr1(substr2(String, S), L).

substr1([C|String], L) when L > 0 -> [C|substr1(String, L-1)];
substr1(String, _L) when is_list(String) -> [].

substr2(String, 1) when is_list(String) -> String;
substr2([_|String], S) -> substr2(String, S-1).

tokens(S, Seps) ->
    case Seps of
        [] ->
            case S of
                [] -> [];
                [_|_] -> [S]
            end;
        [C] ->
            tokens_single_1(lists:reverse(S), C, []);
        [_|_] ->
            tokens_multiple_1(lists:reverse(S), Seps, [])
    end.

tokens_single_1([Sep|S], Sep, Toks) ->
    tokens_single_1(S, Sep, Toks);
tokens_single_1([C|S], Sep, Toks) ->
    tokens_single_2(S, Sep, Toks, [C]);
tokens_single_1([], _, Toks) ->
    Toks.

tokens_single_2([Sep|S], Sep, Toks, Tok) ->
    tokens_single_1(S, Sep, [Tok|Toks]);
tokens_single_2([C|S], Sep, Toks, Tok) ->
    tokens_single_2(S, Sep, Toks, [C|Tok]);
tokens_single_2([], _Sep, Toks, Tok) ->
    [Tok|Toks].

tokens_multiple_1([C|S], Seps, Toks) ->
    case member(C, Seps) of
        true -> tokens_multiple_1(S, Seps, Toks);
        false -> tokens_multiple_2(S, Seps, Toks, [C])
    end;
tokens_multiple_1([], _Seps, Toks) ->
    Toks.

tokens_multiple_2([C|S], Seps, Toks, Tok) ->
    case member(C, Seps) of
        true -> tokens_multiple_1(S, Seps, [Tok|Toks]);
        false -> tokens_multiple_2(S, Seps, Toks, [C|Tok])
    end;
tokens_multiple_2([], _Seps, Toks, Tok) ->
    [Tok|Toks].

chars(C, N) -> chars(C, N, []).

chars(C, N, Tail) when N > 0 ->
    chars(C, N-1, [C|Tail]);
chars(C, 0, Tail) when is_integer(C) ->
    Tail.

copies(CharList, Num) when is_list(CharList), is_integer(Num), Num >= 0 ->
    copies(CharList, Num, []).

copies(_CharList, 0, R) ->
    R;
copies(CharList, Num, R) ->
    copies(CharList, Num-1, CharList++R).

words(String) -> words(String, $\s).

words(String, Char) when is_integer(Char) ->
    w_count(strip(String, both, Char), Char, 0).

w_count([], _, Num) -> Num+1;
w_count([H|T], H, Num) -> w_count(strip(T, left, H), H, Num+1);
w_count([_H|T], Char, Num) -> w_count(T, Char, Num).

sub_word(String, Index) -> sub_word(String, Index, $\s).

sub_word(String, Index, Char) when is_integer(Index), is_integer(Char) ->
    case words(String, Char) of
        Num when Num < Index ->
            [];
        _Num ->
            s_word(strip(String, left, Char), Index, Char, 1, [])
    end.

s_word([], _, _, _, Res) -> lists:reverse(Res);
s_word([Char|_], Index, Char, Index, Res) -> lists:reverse(Res);
s_word([H|T], Index, Char, Index, Res) -> s_word(T, Index, Char, Index, [H|Res]);
s_word([Char|T], Stop, Char, Index, Res) when Index < Stop ->
    s_word(strip(T, left, Char), Stop, Char, Index+1, Res);
s_word([_|T], Stop, Char, Index, Res) when Index < Stop ->
    s_word(T, Stop, Char, Index, Res).

strip(String) -> strip(String, both).

strip(String, left) -> strip_left(String, $\s);
strip(String, right) -> strip_right(String, $\s);
strip(String, both) ->
    strip_right(strip_left(String, $\s), $\s).

strip(String, right, Char) -> strip_right(String, Char);
strip(String, left, Char) -> strip_left(String, Char);
strip(String, both, Char) ->
    strip_right(strip_left(String, Char), Char).

strip_left([Sc|S], Sc) ->
    strip_left(S, Sc);
strip_left([_|_]=S, Sc) when is_integer(Sc) -> S;
strip_left([], Sc) when is_integer(Sc) -> [].

strip_right([Sc|S], Sc) ->
    case strip_right(S, Sc) of
        [] -> [];
        T  -> [Sc|T]
    end;
strip_right([C|S], Sc) ->
    [C|strip_right(S, Sc)];
strip_right([], Sc) when is_integer(Sc) ->
    [].

left(String, Len) when is_integer(Len) -> left(String, Len, $\s).

left(String, Len, Char) when is_integer(Char) ->
    Slen = erlang:length(String),
    if
        Slen > Len -> substr(String, 1, Len);
        Slen < Len -> l_pad(String, Len-Slen, Char);
        Slen =:= Len -> String
    end.

l_pad(String, Num, Char) -> String ++ chars(Char, Num).

right(String, Len) when is_integer(Len) -> right(String, Len, $\s).

right(String, Len, Char) when is_integer(Char) ->
    Slen = erlang:length(String),
    if
        Slen > Len -> substr(String, Slen-Len+1);
        Slen < Len -> r_pad(String, Len-Slen, Char);
        Slen =:= Len -> String
    end.

r_pad(String, Num, Char) -> chars(Char, Num, String).

centre(String, Len) when is_integer(Len) -> centre(String, Len, $\s).

centre(String, 0, Char) when is_list(String), is_integer(Char) ->
    [];
centre(String, Len, Char) when is_integer(Char) ->
    Slen = erlang:length(String),
    if
        Slen > Len -> substr(String, (Slen-Len) div 2 + 1, Len);
        Slen < Len ->
            N = (Len-Slen) div 2,
            r_pad(l_pad(String, Len-(Slen+N), Char), N, Char);
        Slen =:= Len -> String
    end.

sub_string(String, Start) -> substr(String, Start).

sub_string(String, Start, Stop) -> substr(String, Start, Stop - Start + 1).

to_lower_char(C) when is_integer(C), $A =< C, C =< $Z ->
    C + 32;
to_lower_char(C) when is_integer(C), 16#C0 =< C, C =< 16#D6 ->
    C + 32;
to_lower_char(C) when is_integer(C), 16#D8 =< C, C =< 16#DE ->
    C + 32;
to_lower_char(C) ->
    C.

to_upper_char(C) when is_integer(C), $a =< C, C =< $z ->
    C - 32;
to_upper_char(C) when is_integer(C), 16#E0 =< C, C =< 16#F6 ->
    C - 32;
to_upper_char(C) when is_integer(C), 16#F8 =< C, C =< 16#FE ->
    C - 32;
to_upper_char(C) ->
    C.

to_lower(S) when is_list(S) ->
    [to_lower_char(C) || C <- S];
to_lower(C) when is_integer(C) ->
    to_lower_char(C).

to_upper(S) when is_list(S) ->
    [to_upper_char(C) || C <- S];
to_upper(C) when is_integer(C) ->
    to_upper_char(C).

join([], Sep) when is_list(Sep) ->
    [];
join([H|T], Sep) ->
    H ++ lists:append([Sep ++ X || X <- T]).
