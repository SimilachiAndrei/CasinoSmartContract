datatype State = IDLE | GAME_AVAILABLE | BET_PLACED

datatype Coin = HEADS | TAILS

class Contract {
  var name: string
  var operator: string
  var state: State
  var guess: Coin
  var pot: int
  var bet: int
  var player: string
  var hashedNumber: int

  ghost method transfer(amount : int, sender: string)
  ghost function cryptohash(number: int) : int

  function getCoinFromGuess(guess: bool) : Coin{
    if guess == true then TAILS
    else HEADS
  }


  constructor(sender: string, guess: Coin) {
    this.operator := sender;
    this.guess := guess;
    this.state := IDLE;
    this.pot := 0;
    this.bet := 0;
  }

  method addToPot(amount: int, sender: string)
    requires amount > 0
    modifies this
    requires this.operator == sender
  {
    this.pot := this.pot + amount;
  }

  method removeFromPot(amount: int, sender: string)
    modifies this
    requires this.state != BET_PLACED
    requires this.operator == sender
    requires amount > 0
  {
    this.transfer(amount,operator);
    this.pot := pot - amount;
  }


  method createGame(sender: string, hashedNumber: int)
    requires this.state == IDLE
    requires this.operator == sender
    modifies this
  {
    this.hashedNumber := hashedNumber;
    this.state := GAME_AVAILABLE;
  }

  method placeBet(guess : Coin, sender: string, amount: int)
    requires state == GAME_AVAILABLE
    requires sender != this.operator
    requires 0 < amount <= this.pot
    modifies this
  {
    this.state := BET_PLACED;
    this.player := sender;

    this.bet := amount;
    this.guess := guess;
  }

  method decideBet(sender: string, secretNumber: int)
    requires this.state == BET_PLACED
    requires this.operator == sender
    requires this.cryptohash(secretNumber) == this.hashedNumber
    modifies this
  {
    var secret: Coin := getCoinFromGuess((secretNumber % 2) == 0);
    if secret == this.guess {
      // Player wins
      this.pot := this.pot - this.bet;
      this.transfer(2 * this.bet, this.player);
    } else {
      // Operator wins
      this.pot := this.pot + this.bet;
    }
    this.bet := 0;
    this.state := IDLE;
  }

}

