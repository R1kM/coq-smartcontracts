contract Auction {
    int public highestBid;

    mapping (address => bool) public isWinner; 
    mapping (address => int) public bids;

    function Auction (){
        highestBid = 0;
        isWinner[msg.sender] = true;
    }

    function bid(int value) {
        if (bids[msg.sender] > value) throw;
        else {
            bids[msg.sender] = value;
            if (value > highestBid) {
                highestBid = value;
                isWinner[msg.sender] = true;
            }
        }
    }

    function get_money() {
        if (isWinner[msg.sender]) {
            msg.sender.send(highestBid);
            isWinner[msg.sender] = false;
        }
    }
        
}
