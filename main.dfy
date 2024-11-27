datatype State = IDLE | GAME_AVAILABLE | BET_PLACED

datatype Coin = HEADS | TAILS

class Sender {
  var name: string
  var balance: int

  constructor() 
  ensures this.balance >= 0
  {
    this.name := "";
    this.balance := 0;
  }

  constructor FromName(name: string)
  ensures this.balance >= 0 
  {
    this.name := name;
    this.balance := 0;
  }

  lemma smth(a: int, b: int, c: int)
    requires a > 0 && b > 0 && c >0
  {
  }

  method transfer(person: Sender, amount: int)
    modifies this, person
    requires 0 < amount <= this.balance
    // ensures forall a: int,b : int {:trigger} :: 0 <a && 0 < b ==> a + b >= a ==> person.balance >= person.balance + amount
  {
    this.balance := this.balance - amount;
    person.balance := person.balance + amount;
  }

  predicate equals(person: Sender)
    reads this, person
  {
    this.name == person.name
  }
}

class Contract {
  var name: string
  var operator: Sender
  var state: State
  var guess: Coin
  var pot: int
  var bet: int
  var player: Sender
  var hashedNumber: int

  ghost function cryptohash(number: int) : int

  function getCoinFromGuess(guess: bool) : Coin{
    if guess == true then TAILS
    else HEADS
  }


  constructor(sender: Sender, guess: Coin)
  {
    this.operator := sender;
    this.guess := guess;
    this.state := IDLE;
    this.pot := 0;
    this.bet := 0;
    this.player := new Sender();
  }

  method addToPot(sender: Sender, amount: int)
    requires 0 < amount <= sender.balance
    modifies this
    modifies this.operator
    requires this.operator.equals(sender) == true
  {
    this.operator.balance := this.operator.balance - amount;
    this.pot := this.pot + amount;
  }

  method removeFromPot(sender: Sender, amount: int)
    modifies this
    modifies this.operator
    // requires this.state != BET_PLACED
    requires this.operator.equals(sender) == true
    // requires 0 < this.bet < this.pot / 2
  {
    this.operator.balance := this.operator.balance + amount;
    this.pot := pot - amount;
  }


  method createGame(sender: Sender, hashedNumber: int)
    requires this.state == IDLE
    requires this.operator.equals(sender) == true
    modifies this
  {
    this.hashedNumber := hashedNumber;
    this.state := GAME_AVAILABLE;
  }

  method placeBet(sender: Sender, guess : Coin, amount: int)
    requires state == GAME_AVAILABLE
    requires sender.equals(this.operator) == false
    requires 0 < amount <= sender.balance

    modifies this
    modifies this.operator
    modifies sender
  {
    this.state := BET_PLACED;
    this.player := sender;
    sender.transfer(this.operator, amount);
    // this.addToPot(this.operator, amount);

    this.bet := amount;
    this.guess := guess;
  }

  method decideBet(sender: Sender, secretNumber: int)
    requires this.state == BET_PLACED
    requires this.operator == sender
    requires this.cryptohash(secretNumber) == this.hashedNumber
    modifies this
    modifies this.operator
  {
    var secret: Coin := getCoinFromGuess((secretNumber % 2) == 0);
    if secret == this.guess {
      // Player wins
      // this.pot := this.pot - this.bet;
      // this.player.balance := this.player.balance + 2 * this.bet;
      this.removeFromPot(operator, 2* this.bet);
      // this.operator.transfer(this.player, 2 * this.bet);
    } else {
      // Operator wins
      // this.player.transfer(this.operator, this.bet);
      // this.addToPot(this.operator, this.bet);
    }
    this.bet := 0;
    this.state := IDLE;
  }

}

