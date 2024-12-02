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
  constructor FromNameBalance(name: string, balance: int)
    requires balance > 0
    ensures this.balance ==balance
  {
    this.name := name;
    this.balance := balance;
  }

  method transfer(person: Sender, amount: int)
    requires person != this
    modifies this, person
    requires this != person
    requires 0 < amount <= this.balance
    requires person.balance >= 0
    ensures this.balance ==  old(this.balance) - amount
    ensures person.balance == old(person.balance) + amount
    ensures old(person.balance) <= person.balance
    ensures old(person.balance) <= person.balance + amount
    ensures amount <= person.balance
    ensures this.balance >= 0
    ensures person.balance >= 0
  {

    this.balance := this.balance - amount;
    person.balance := person.balance + amount;
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
  ensures this.operator != this.player
  {
    this.operator := sender;
    this.guess := guess;
    this.state := IDLE;
    this.pot := 0;
    this.bet := 0;
    this.player := new Sender();
  }

  method removeFromPot(sender: Sender, amount: int)
    modifies this, this.operator
    requires this.operator.balance >= 0
    requires this.bet > 0
    requires 2 * this.bet == amount
    // requires this.state != BET_PLACED
    requires this.operator == sender
    requires this.operator != this.player
    ensures this.operator != this.player
    ensures 0 < this.bet <= this.operator.balance
    ensures 0 < 2 * this.bet <= this.operator.balance
    ensures old(this.player) == this.player
    ensures this.operator == sender
    // requires 0 < this.bet < this.pot / 2
  { 
    this.operator.balance := this.operator.balance + amount;
    this.pot := pot - amount;
  }


  method createGame(sender: Sender, hashedNumber: int)
    requires this.state == IDLE
    requires this.operator == sender
    modifies this
  {
    this.hashedNumber := hashedNumber;
    this.state := GAME_AVAILABLE;
  }

  method addToPot(sender: Sender, amount: int)
    requires 0 < amount <= sender.balance
    modifies this, this.operator
    requires sender == this.operator
    ensures sender.balance == operator.balance
    // ensures this.operator.balance - amount >= 0
  {
    this.operator.balance := this.operator.balance - amount;
    this.pot := this.pot + amount;
  }

  method placeBet(sender: Sender, guess : Coin, amount: int)
    requires state == GAME_AVAILABLE
    requires sender != this.operator
    requires 0 < amount <= sender.balance
    requires this.operator.balance > 0

    modifies this, sender, this.operator
    // ensures 0 < this.bet <= sender.balance
  {

    this.state := BET_PLACED;
    this.player := sender;

    sender.transfer(this.operator, amount);

    this.addToPot(this.operator, amount);

    this.bet := amount;
    this.guess := guess;
  }

  method decideBet(sender: Sender, secretNumber: int)
    requires this.state == BET_PLACED
    requires this.operator == sender
    requires this.cryptohash(secretNumber) == this.hashedNumber
    requires 0 < this.bet <= sender.balance
    requires this.player != this.operator
    requires this.bet <= this.player.balance
    modifies this, this.operator, this.player

  {
    var secret: Coin := getCoinFromGuess((secretNumber % 2) == 0);
    if secret == this.guess {
      // Player wins
      this.pot := this.pot - this.bet;
      this.player.balance := this.player.balance + 2 * this.bet;
      this.removeFromPot(this.operator, 2* this.bet);
      this.operator.transfer(this.player, 2 * this.bet);
    } else {
      // Operator wins
      this.player.transfer(this.operator, this.bet);
      this.addToPot(this.operator, this.bet);
    }
    this.bet := 0;
    this.state := IDLE;
  }

}

