% a module is a collection of function
-module(lcr).
% list of exported function (ie. visible outside of the module),
% together with their arity
-export([proc/1]).

% a record is a like C struct
% we define a record type "state" with two fields, uin, and neighbors
% 0 and nil are default values used when a record is created (#state{})
% nil is an "atom" (all ids starting with lowercase letters are atoms
-record(state,
    { uin = 0,
      neighbors = nil
    }).

% definition of a (local) function taking two parameters U and Neighbors.
% in Erlang, all variables identifiers start with an upper case letter
% Warning: this is error prone
% notice the Prolog syntax: fun(X0, ... Xn) -> C1, C2, ..., Cm.
% U is an arbitrary value
% Neighbors of a list of process identifiers
broadcast(U, Neighbors) ->
    % equivalent of printf function
    % self() returns the ID of the current process
    io:format("~w broadcasts value ~w to neighbors~w~n", [self(), U, Neighbors]),
    % if X is an ID, X ! V sends the value V to X.
    % we can construct tuple with {   }
    % note the use of atom msg
    F = fun(X) -> X ! {msg, U} end,
    % apply F to the each elements of the list Neighbors
    lists : map(F , Neighbors).

% This is the main function of the process. Erlang is pure functional, so we use
% a parameter (here a record) to carry the global state of the process, and a
% (tail)-recursive function to realize a loop. This function is an event-loop.
% It constantly checks for messaged sent to the current process via the sending
% construct.  messages are kept in a FIFO buffer until read by the receive
% construct
%
% After a process is created, a global controler initializes its state before
% the algorithm can be ran.  This is done in three steps by the "control : init"
% function.
%
% 1 - sending of init_state message: State is now a state record 2 - sending of
% { neighbors, N, Sender } messages. Recall that neighbors is just an atom that
% let the pattern matcher knows the message type.  N contains the list of actual
% neighbors of this process (should be only one for a uni-ring topology) Sender
% is the Id of the Sender (controler). It is used to inform the controler that
% initialized has been done.  3 - sending of additional algorithm-dependant
% information (the UIN of the process in LCR)
%
% when this has been done, sending of message "start" to initiate the algorithm
proc(State) ->
    % receive uses pattern matching to process messages
    % notice the ";" to separate each cases.
    receive
        init_state -> proc(#state{});
        { neighbors, N, Sender } ->
            io:format("~w is initialized with neighbors ~w~n", [self(), N]),
            Sender ! ok,
            % State#state{neighbors = N} is a record equals to State
            % but with neighbors field updated with N
            proc(State#state{neighbors = N}) ;
        { init, U, Sender } ->
            io:format("~w is initialized with UIN ~w~n", [self(), U]),
            Sender ! ok,
            proc(State#state{uin = U}) ;
        start ->
            io:format("~w is starting leader election algorithm~n", [self()]),
            broadcast(State#state.uin, State#state.neighbors),
            proc(State);
        { msg, U } ->
            io:format("~w received message ~w~n", [self(), U]),
            if
                U > State#state.uin ->
                    broadcast(U, State#state.neighbors),
                    proc(State);
                U == State#state.uin ->
                    io:format("~w is the leader ~n", [self()]),
                    proc(State);
                U < State#state.uin -> proc(State)
            end;
        quit ->
            io:format("~w says bye bye!~n", [self()])
    end,
    ok.
