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
    ensures this.balance == balance
    ensures this.balance > 0
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

  function cryptohash(number: int) : (o:int)
    ensures cryptohash(number) >= 0
    ensures o == cryptohash(number)
  {
    if number < 0 then -(number * 31 + 17) else number * 31 + 17
  }

  function getCoinFromGuess(guess: bool) : Coin{
    if guess == true then TAILS
    else HEADS
  }


  constructor(sender: Sender, guess: Coin)
    ensures this.operator != this.player
    ensures this.state == IDLE
    ensures this.operator == sender
    ensures this.bet == 0
    ensures this.pot == 0
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
    requires 0 < amount <= this.pot
    // requires this.state != BET_PLACED
    requires this.operator == sender
    requires this.operator != this.player
    ensures this.operator != this.player
    ensures old(this.player) == this.player
    ensures this.operator == sender
    ensures old(this.bet) == this.bet
    ensures this.operator.balance == old(this.operator.balance) + amount
    // requires 0 < this.bet < this.pot / 2
  {
    this.operator.balance := this.operator.balance + amount;
    this.pot := pot - amount;
  }


  method createGame(sender: Sender, hashedNumber: int)
    requires this.state == IDLE
    requires this.operator == sender
    requires this.player != this.operator
    requires operator.balance > 0
    requires this.bet == 0
    requires this.pot == 0
    modifies this
    ensures this.state == GAME_AVAILABLE
    ensures this.operator.balance > 0
    ensures this.player != this.operator
    ensures this.operator == old(this.operator)
    ensures this.hashedNumber == hashedNumber
    ensures this.bet == 0
    ensures this.pot == 0
  {
    this.hashedNumber := hashedNumber;
    this.state := GAME_AVAILABLE;
  }

  method addToPot(sender: Sender, amount: int)
    requires 0 < amount <= sender.balance
    requires sender == this.operator
    modifies this, this.operator
    ensures sender.balance == operator.balance
    ensures old(this.state) == this.state
    ensures this.operator == old(this.operator)
    ensures old(this.player) == this.player
    ensures this.operator.balance >= 0
    ensures this.hashedNumber == old(this.hashedNumber)
    ensures this.pot == old(this.pot) + amount
    ensures this.bet == old(this.bet)
    // ensures this.operator != this.player
    // ensures this.operator.balance - amount >= 0
  {
    this.operator.balance := this.operator.balance - amount;
    this.pot := this.pot + amount;
  }

  method placeBet(sender: Sender, guess : Coin, amount: int)
    requires state == GAME_AVAILABLE
    requires sender != this.operator
    requires 0 < amount <= sender.balance
    requires this.operator.balance >= 0
    requires this.pot >= 2 * amount


    modifies this, sender, this.operator
    // ensures 0 < this.bet <= sender.balance
    ensures this.state == BET_PLACED
    ensures this.operator == old(this.operator)
    ensures this.bet > 0
    ensures this.player == sender
    ensures this.player.balance >= 0
    ensures this.operator.balance >= 0
    ensures this.hashedNumber == old(this.hashedNumber)
    ensures this.pot >= 2 * this.bet
    // ensures this.operator != this.player
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
    requires this.bet > 0
    // requires 0 < this.bet && 0 < operator.balance
    requires this.player != this.operator
    // requires this.bet <= this.player.balance
    requires this.operator.balance >= 0
    requires this.player.balance >= 0
    requires this.pot >= 2 * this.bet
    modifies this, this.operator, this.player
    
  {
    var secret: Coin := getCoinFromGuess((secretNumber % 2) == 0);
    if secret == this.guess {
      // Player wins
      this.removeFromPot(this.operator, 2* this.bet);
      this.operator.transfer(this.player, 2 * this.bet);
    } 
    // else {
    //   // Operator wins
    //   this.player.transfer(this.operator, this.bet);
    //   this.addToPot(this.operator, this.bet);
    // }
    this.bet := 0;
    this.state := IDLE;
  }

}

method Main()
{
  var operator := new Sender.FromNameBalance("Operator", 100);
  var player := new Sender.FromNameBalance("Player", 50);

  var contract := new Contract(operator, HEADS);

  var secretNumber := 42;

  var hashedNumber := contract.cryptohash(secretNumber);
  contract.createGame(contract.operator, hashedNumber);

  contract.addToPot(contract.operator,50);
  
  contract.placeBet(player, TAILS, 10); 

  contract.decideBet(contract.operator, 41); 

  print "Operator balance: "; print contract.operator.balance; print "\n";
  print "Player balance: "; print player.balance; print "\n";
  print "Contract state: "; print contract.state; print "\n";
  print "Pot: "; print contract.pot; print "\n";

}
