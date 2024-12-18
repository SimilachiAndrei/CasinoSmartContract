datatype Coin = HEADS | TAILS

datatype State = IDLE | GAME_AVAILABLE | BET_PLACED

datatype Msg = Msg(sender: Account, value: int) 


trait Account {
  var balance: int
  var address: string

  method transfer(to: Account, amount: int)
    requires to != this
    requires 0 < amount <= this.balance
    requires to.balance >= 0
    modifies this, to
    // ensures this.balance == old(this.balance) - amount
    // ensures to.balance == old(to.balance) + amount
  {
    this.balance := this.balance - amount;
    to.balance := to.balance + amount;
  }
}

class UserAccount extends Account {

    constructor(initialBal: int) 
        ensures balance == initialBal
    {
        balance := initialBal;
    }
}

class Casino extends Account{
  var operator: Account
  var player: Account
  var pot: int
  var hashedNumber: int
  var guess: Coin
  var bet: int
  var state: State

  function cryptohash(number: int): int
    ensures cryptohash(number) >= 0
  {
    if number < 0 then -(number * 31 + 17) else number * 31 + 17
  }

  function getCoinFromNumber(number: int): Coin {
    if number % 2 == 0 then HEADS else TAILS
  }

  constructor(msg: Msg)
    ensures this.operator == msg.sender
    ensures this.state == IDLE
    ensures this.pot == 0
    ensures this.bet == 0
    ensures this != this.operator
    ensures this != player
    ensures this.balance >= 0
  {
    this.balance := 0;
    this.operator := msg.sender;
    this.state := IDLE;
    this.pot := 0;
    this.bet := 0;
    this.player := new UserAccount(0);
  }

  method addToPot(msg: Msg)
    requires msg.sender == this.operator
    requires 0 < msg.value <= this.operator.balance
    requires msg.sender != this
    requires this.balance >= 0
    modifies this, this.operator
    // ensures this.pot == old(this.pot) + msg.value
    // ensures this.operator.balance == old(this.operator.balance) - msg.value
  {
    this.operator.transfer(this, msg.value);
    // this.operator.balance := this.operator.balance - msg.value;
    this.pot := this.pot + msg.value;
  }

  method removeFromPot(msg: Msg, amount: int)
    requires this.state != BET_PLACED
    requires msg.sender == this.operator
    requires 0 < amount <= this.balance
    requires msg.sender != this
    requires this.operator.balance >= 0
    modifies this, this.operator
    // ensures this.pot == old(this.pot) - amount
    // ensures this.operator.balance == old(this.operator.balance) + amount
  {
    // assert this.operator.balance >= 0;
    this.transfer(this.operator,amount);
    this.pot := this.pot - amount;
  }

  method createGame(msg: Msg, hashedNumber: int)
    requires this.state == IDLE
    requires msg.sender == this.operator
    requires msg.sender != this
    modifies this
    ensures this.state == GAME_AVAILABLE
    ensures this.hashedNumber == hashedNumber
  {
    this.hashedNumber := hashedNumber;
    this.state := GAME_AVAILABLE;
  }

  method placeBet(msg: Msg, guess: Coin)
    requires this.state == GAME_AVAILABLE
    requires msg.sender != this.operator
    requires msg.sender != this
    requires 0 < msg.value <= msg.sender.balance
    requires this.balance >= 0
    modifies this, msg.sender
    ensures this.state == BET_PLACED
    ensures this.bet == msg.value
    ensures this.player == msg.sender
    ensures this.guess == guess
  {
    //payable ??? inainte sau dupa
    // this.player.balance := this.player.balance - msg.value;
    // this.pot := this.pot + msg.value;
    msg.sender.transfer(this, msg.value);
    this.state := BET_PLACED;
    this.player := msg.sender;
    this.bet := msg.value;
    this.guess := guess;
  }

  method decideBet(msg: Msg, secretNumber: int)
    requires this.state == BET_PLACED
    requires msg.sender == this.operator
    requires cryptohash(secretNumber) == this.hashedNumber
    requires msg.sender != this && player != this
    requires this.player.balance >= 0
    requires 0 < 2 * this.bet <= this.balance
    modifies this, this.operator, this.player
    ensures this.state == IDLE
    ensures this.bet == 0
  {
    var secret: Coin := getCoinFromNumber(secretNumber);

    if secret == this.guess {
      // Player wins
      this.pot := this.pot - this.bet;
      this.transfer(this.player, 2 * this.bet);
    } else {
      // Operator wins
      this.pot := this.pot + this.bet;
    }
    this.bet := 0;
    this.state := IDLE;
  }
}

