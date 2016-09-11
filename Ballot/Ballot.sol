contract Ballot {
    // Create a new ballot with $(_numProposals) different proposals.
    function Ballot(uint8 _numProposals) {
        chairperson = sender;
        numProposals = _numProposals;
    }

    // Give $(voter) the right to vote on this ballot.
    // May only be called by $(chairperson).
    function giveRightToVote(address voter) {
        if (/*msg.sender != chairperson ||*/ voted[voter]) return;
        voterWeight[voter] = 1;
    }

    // Delegate your vote to the voter $(to).
    function delegate(address to) {
        if (voted[sender]) return;
        if (to == sender) return;
        voted[sender] = true;
        delegations[sender] = to;
        if (voted[to]) voteCounts[votes[to]] += voterWeight[sender];
        else {voterWeight[to] += voterWeight[sender];
             voterWeight[sender] = 0;}
    }

    // Give a single vote to proposal $(proposal).
    function vote(uint8 proposal) {
        if (voted[sender] || proposal >= numProposals) return;
        voted[sender] = true;
        votes[sender] = proposal;
        voteCounts[proposal] += voterWeight[sender];
    }

    address chairperson;
    uint8 numProposals;
    mapping(address => uint256) voterWeight;
    mapping(address => bool) voted;
    mapping(address => uint8) votes;
    mapping(address => address) delegations;
    mapping(uint8 => uint256) voteCounts;
}


