%% Author: Kristian Poslek
%% Created: 2009.04.09
%% Renamed from peer.erl to chord_peer.erl for CerlEx testing — avoids
%% shadowing OTP 25's built-in peer module during Concuerror runs.

-module(chord_peer).
-export([add/1, add/2, start/2, start/3, loop/5]).

%% +++++++++++++++++++++++ add/1
%% Used for the first peer entering the ring.
add(Name) ->
	PeerKey = helper:hash(Name),
	NextPeerKey = helper:hash(Name),
	spawn(chord_peer, start, [Name, PeerKey, NextPeerKey]).


%% +++++++++++++++++++++++ start/3
%% Only used for starting the first peer.
start(Name, PeerKey, NextPeerKey) ->
	ListOfFiles = [],
	loop(Name, PeerKey, NextPeerKey, self(), ListOfFiles).


%% +++++++++++++++++++++++ add/2
%% Used for every other peer entering the ring.
add(Name, KnownNode) ->
	spawn(chord_peer, start, [Name, KnownNode]).
	

%% +++++++++++++++++++++++ start/2
%% This type of start is used for starting any peer that isn't the first to enter the ring.
%% This is neccessary because a process gets its PID only after it spawns.
start(Name, KnownNode) ->
	PeerKey = helper:hash(Name),
	KnownNode!{enterRing, self(), PeerKey, Name},
	receive
		{enteredRing, NextPeerKey, NextPeerID, ListOfFiles} ->
			loop(Name, PeerKey, NextPeerKey, NextPeerID, ListOfFiles)
	end.


%% +++++++++++++++++++++++ loop/5
%% loop() is the main behaviour of each peer. Each peer listens to incoming
%% messages and reacts upon them.
loop(Name, PeerKey, NextPeerKey, NextPeerID, ListOfFiles) ->
	receive
		%% Display the status of the messaged peer.
		status ->
			loop(Name, PeerKey, NextPeerKey, NextPeerID, ListOfFiles);
		
		%% Used to help a new peer enter the ring.
		%% KeyStatus checks if the entering peer is at its designed location or if we need to
		%% go check with the next peer.
		{enterRing, From, FromKey, FromName} ->
			KeyStatus = helper:isNextPeer(FromKey, PeerKey, NextPeerKey),
			if
				%% The key of the entering peer is in a range that's lower than the current range.
				KeyStatus == lower ->
					NextPeerID!{enterRing, From, FromKey, FromName},
					loop(Name, PeerKey, NextPeerKey, NextPeerID, ListOfFiles);
				%% This key already exists in the system.
				KeyStatus == same ->
					ok;
				%% The key of the entering peer is in a range that's higher than the current range.
				KeyStatus == greater ->
					NextPeerID!{enterRing, From, FromKey, FromName},
					loop(Name, PeerKey, NextPeerKey, NextPeerID, ListOfFiles);
				%% The key of the entering peer is in the current range.
				KeyStatus == found ->
					LowerListOfFiles = helper:extractLowerElements(ListOfFiles, FromKey),
					HigherListOfFiles = helper:extractHigherElements(ListOfFiles, FromKey),
					From!{enteredRing, NextPeerKey, NextPeerID, HigherListOfFiles},
					loop(Name, PeerKey, FromKey, From, LowerListOfFiles);
				%% The entering peer is the last peer in the ring.
				KeyStatus == foundLast ->
					LowerListOfFiles = helper:extractLowerElements(ListOfFiles, FromKey),
					HigherListOfFiles = helper:extractHigherElements(ListOfFiles, FromKey),
					From!{enteredRing, NextPeerKey, NextPeerID, HigherListOfFiles},
					loop(Name, PeerKey, FromKey, From, LowerListOfFiles);
				%% The entering peer is the first peer in the ring.
				KeyStatus == foundFirst ->
					LowerListOfFilesTemp = helper:extractLowerElements(ListOfFiles, NextPeerKey),
					HigherListOfFilesTemp = helper:extractHigherElements(ListOfFiles, NextPeerKey),
					LowerListOfFiles = helper:extractHigherElements(LowerListOfFilesTemp, FromKey),
					HigherListOfFiles = lists:merge(helper:extractLowerElements(LowerListOfFilesTemp, FromKey), HigherListOfFilesTemp),
					From!{enteredRing, NextPeerKey, NextPeerID, LowerListOfFiles},
					loop(Name, PeerKey, FromKey, From, HigherListOfFiles)
			end;
		
		%% Add a new resource.
		{put, Resource} ->
			ResourceKey = helper:hash(Resource),
			%% Lookup if the resource belongs to the current peer.
			IsInRange = helper:lookup(ResourceKey, PeerKey, NextPeerKey),
			if
				%% Add to the list if the resource is at the right key range.
				IsInRange == true ->
					NewListOfFiles = lists:sort([{ResourceKey, Resource}|ListOfFiles]),
					loop(Name, PeerKey, NextPeerKey, NextPeerID, NewListOfFiles);
				%% Ask the next peer if the key isn't in this key range.
				IsInRange == false ->
					NextPeerID!{put, Resource},
					loop(Name, PeerKey, NextPeerKey, NextPeerID, ListOfFiles)
			end;
		
		{get, Resource} ->
			ResourceKey = helper:hash(Resource),
			IsInRange = helper:lookup(ResourceKey, PeerKey, NextPeerKey),
			if
				%% If the requested resource is in the current range.
				IsInRange == true ->
					loop(Name, PeerKey, NextPeerKey, NextPeerID, ListOfFiles);
				%% If the requested resource isn't in the current range.
				IsInRange == false ->
					NextPeerID!{get, Resource},
					loop(Name, PeerKey, NextPeerKey, NextPeerID, ListOfFiles)
			end;
			
		%% End the current peer and inform the other peers.
		stop ->
			NextPeerID!{peerGone, PeerKey, NextPeerKey, NextPeerID, ListOfFiles};

		%% Used to get to the peer before the ending one so that it can establish new connections.
		{peerGone, GonePeerKey, GoneNextPeerKey, GoneNextPeerID, RemainingListOfFiles} ->
			if
				GonePeerKey == NextPeerKey ->
					NewListOfFiles = lists:sort(lists:merge(ListOfFiles, RemainingListOfFiles)),
					loop(Name, PeerKey, GoneNextPeerKey, GoneNextPeerID, NewListOfFiles);
				true ->
					NextPeerID!{peerGone, GonePeerKey, GoneNextPeerKey, GoneNextPeerID, RemainingListOfFiles},
					loop(Name, PeerKey, NextPeerKey, NextPeerID, ListOfFiles)
			end;
	
		%% Used to display the whole ring of peers, starting with the peer that called showRing.
		showRing ->
			NextPeerID!{showRing, PeerKey},
			loop(Name, PeerKey, NextPeerKey, NextPeerID, ListOfFiles);
			
		{showRing, FirstPeerKey} ->
			if
				PeerKey == FirstPeerKey ->
					loop(Name, PeerKey, NextPeerKey, NextPeerID, ListOfFiles);
				true ->
					NextPeerID!{showRing, FirstPeerKey},
					loop(Name, PeerKey, NextPeerKey, NextPeerID, ListOfFiles)
			end				
					

	end.
