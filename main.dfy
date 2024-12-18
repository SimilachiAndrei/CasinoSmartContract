datatype Coin = HEADS | TAILS

datatype State = IDLE | GAME_AVAILABLE | BET_PLACED

datatype Msg = Msg(sender: Account, value: int)

datatype Try<T> = Success(v: T) | Revert()

trait Account {
  var balance: int
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

  function {:axiom} cryptohash(number: int): int
    ensures cryptohash(number) >= 0
  // {
  //   if number < 0 then -(number * 31 + 17) else number * 31 + 17
  // }

  function getCoinFromNumber(number: int): Coin {
    if number % 2 == 0 then HEADS else TAILS
  }

  ghost predicate GInv() 
  reads this
  {
    this.pot >= 0 &&
    this.balance >= 0 &&
    (this.state != BET_PLACED || this.bet > 0)
  }


  constructor(msg: Msg)
    ensures this.operator == msg.sender
    ensures this.state == IDLE
    ensures this.pot == 0
    ensures this.bet == 0
    ensures this != this.operator
    ensures this != player
    ensures this.balance >= 0
    ensures GInv()
  {
    this.balance := 0;
    this.operator := msg.sender;
    this.state := IDLE;
    this.pot := 0;
    this.bet := 0;
    this.player := new UserAccount(0);
  }

    method transfer(from: Account, to: Account, amount: int)
    requires GInv()
    requires to != from
    requires 0 < amount <= from.balance
    requires to.balance >= 0
    modifies from, to
    ensures from.balance == old(from.balance) - amount
    ensures to.balance == old(to.balance) + amount
    ensures old(this.pot) == this.pot
    ensures GInv()
  {
    from.balance := from.balance - amount;
    to.balance := to.balance + amount;
  }

  method addToPot(msg: Msg)
    requires GInv()
    requires msg.sender == this.operator
    requires 0 < msg.value <= this.operator.balance
    requires msg.sender != this
    requires this.balance >= 0
    modifies this, this.operator
    ensures GInv()
    // ensures this.pot == old(this.pot) + msg.value
    // ensures this.operator.balance == old(this.operator.balance) - msg.value
  {
    transfer(this.operator, this, msg.value);
    this.pot := this.pot + msg.value;
  }

  method removeFromPot(msg: Msg, amount: int)
    requires GInv()
    requires this.state != BET_PLACED
    requires msg.sender == this.operator
    requires 0 < amount <= this.balance
    requires 0 < amount <= this.pot
    requires msg.sender != this
    requires this.operator.balance >= 0
    modifies this, this.operator
    ensures GInv()
    // ensures this.pot == old(this.pot) - amount
    // ensures this.operator.balance == old(this.operator.balance) + amount
  {
    transfer(this, this.operator,amount);
    this.pot := this.pot - amount;
  }

  method createGame(msg: Msg, hashedNumber: int)
    requires GInv()
    requires this.state == IDLE
    requires msg.sender == this.operator
    requires msg.sender != this
    modifies this
    ensures this.state == GAME_AVAILABLE
    ensures this.hashedNumber == hashedNumber
    ensures GInv()
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
    requires GInv()
    modifies this, msg.sender
    ensures this.state == BET_PLACED
    ensures this.bet == msg.value
    ensures this.player == msg.sender
    ensures this.guess == guess
    ensures GInv()
  {
    transfer(msg.sender, this, msg.value);
    this.state := BET_PLACED;
    this.player := msg.sender;
    this.bet := msg.value;
    this.guess := guess;
  }

  method decideBet(msg: Msg, secretNumber: int)
    requires GInv()
    requires this.state == BET_PLACED
    requires msg.sender == this.operator
    requires cryptohash(secretNumber) == this.hashedNumber
    requires msg.sender != this && player != this
    requires this.player.balance >= 0
    requires 0 < 2 * this.bet <= this.balance
    requires 0 < 2 * this.bet <= this.pot
    modifies this, this.operator, this.player
    ensures this.state == IDLE
    ensures this.bet == 0
    ensures GInv()
  {
    var secret: Coin := getCoinFromNumber(secretNumber);

    if secret == this.guess {
      // Player wins
      this.pot := this.pot - this.bet;
      transfer(this, this.player, 2 * this.bet);
    } else {
      // Operator wins
      this.pot := this.pot + this.bet;
    }
    this.bet := 0;
    this.state := IDLE;
  }

  // method externalCall() returns (r: Try<()>)
  //   requires GInv()
  //   ensures GInv()
  //   modifies this
  // {
  //   var k: nat := havoc();
  //   if k % 2 == 0 {
  //     // Simulate re-entrant `placeBet`
  //     var msg: Msg := havoc();
  //     var newGuess: Coin := havoc();
  //     placeBet(msg, newGuess);
  //   } else if k % 2 == 1  {
  //     // Simulate re-entrant `decideBet`
  //     var msg: Msg := havoc();
  //     var secretNumber: int := havoc();
  //     decideBet(msg, secretNumber);
  //   }
  // }
method {:extern} havoc<T>() returns (a: T)
}

//in loc de requires trebuie verificat cu if si sa poata fi dat revert . trebuie adaugat gas, modificat invariantul global
//sa fie mai bun