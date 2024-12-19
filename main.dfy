//TO DO : totalAmount
//TO DO : maybe use <==> and find some conditions for Success and Revert in some functions
//TO DO : verificare havoc

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

  ghost var totalAmount: nat

  function {:axiom} cryptohash(number: int): int
    ensures cryptohash(number) >= 0
  // {
  //   if number < 0 then -(number * 31 + 17) else number * 31 + 17
  // }

  function getCoinFromNumber(number: int): Coin {
    if number % 2 == 0 then HEADS else TAILS
  }

  ghost predicate GInv()
    reads this, this`totalAmount, this.operator, this.player
  {
    this.pot >= 0 &&
    this.balance >= 0 &&
    (this.state != BET_PLACED || this.bet > 0) // &&
    // totalAmount == this.operator.balance + this.balance
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

  method transfer(from: Account, to: Account, amount: int, gas: nat) returns (g: nat, r: Try<()>)
    requires GInv()
    requires gas >= 1
    modifies from, to
    ensures
      r.Success? <==>
      (from != to && 0 < amount <= old(from.balance) && to.balance >= 0 && gas >= 1 &&
       from.balance == old(from.balance) - amount &&
       to.balance == old(to.balance) + amount &&
       old(this.pot) == this.pot)
    ensures r.Revert? ==>
              (from.balance == old(from.balance) && to.balance == old(to.balance))
    ensures g == 0 || g <= gas - 1
    ensures GInv()
    ensures old(this.state) == this.state && old(this.player) == this.player && old(this.guess) == this.guess
            && old(this.bet)== this.bet && old(this.pot) ==this.pot
    decreases gas
  {
    if !(from != to && 0 < amount <= from.balance && to.balance >= 0) {
      return (if gas >= 1 then gas - 1 else 0), Revert();
    }

    from.balance := from.balance - amount;
    to.balance := to.balance + amount;

    g, r := (gas - 1), Success(());
  }



  method addToPot(msg: Msg, gas: nat) returns (g: nat, r: Try<()>)
    requires GInv()
    requires gas >= 1
    modifies this, this.operator
    //ensures for Succ
    //ensures for Revert
    ensures g == 0 || g <= gas - 1
    ensures GInv()
    decreases gas
  {
    if !(msg.sender == this.operator && 0 < msg.value <= this.operator.balance && msg.sender != this &&
         this.balance >= 0) {
      return (if gas >= 1 then gas - 1 else 0), Revert();
    }

    var tg, tr := transfer(this.operator, this, msg.value, gas);

    if tr.Revert? {
      return (if tg >= 1 then tg - 1 else 0), Revert();
    }

    if tg >= 1 {
      this.pot := this.pot + msg.value;
      g, r := tg - 1, Success(());
    } else {
      return tg, Revert();
    }
  }


  method removeFromPot(msg: Msg, amount: int, gas: nat) returns (g: nat, r: Try<()>)
    requires GInv()
    requires gas >= 1
    modifies this, this.operator
    //ensures for Succ
    //ensures for Revert
    ensures g == 0 || g <= gas - 1
    ensures GInv()
    decreases gas
  {
    if !(this.state == BET_PLACED && msg.sender == this.operator && 0 < amount <= this.balance && 0 < amount <= this.pot
         && msg.sender != this && this.operator.balance >= 0) {
      return (if gas >= 1 then gas - 1 else 0), Revert();
    }

    var tg, tr := transfer(this, this.operator,amount, gas);

    if tr.Revert? {
      return (if tg >= 1 then tg - 1 else 0), Revert();
    }

    if tg >= 1 {
      this.pot := this.pot - amount;
      g, r := tg - 1, Success(());
    } else {
      return tg, Revert();
    }
  }

  method createGame(msg: Msg, hashedNumber: int, gas : nat) returns (g: nat, r: Try<()>)
    requires GInv()
    requires gas >= 1
    modifies this
    ensures r.Success? ==> (this.state == GAME_AVAILABLE && this.hashedNumber == hashedNumber)
    ensures r.Revert? ==>
              (old(this.state) == this.state)
    ensures g == 0 || g <= gas - 1
    ensures GInv()
    decreases gas
  {
    if !(this.state == IDLE && msg.sender == this.operator && msg.sender != this) {
      return (if gas >= 1 then gas - 1 else 0), Revert();
    }
    this.hashedNumber := hashedNumber;
    this.state := GAME_AVAILABLE;
    g, r := (gas - 1), Success(());
  }

  method placeBet(msg: Msg, guess: Coin, gas: nat) returns (g : nat , r : Try<()>)
    requires gas >= 1
    requires GInv()
    modifies this, msg.sender
    ensures r.Success? ==> (this.state == BET_PLACED && this.bet == msg.value && this.player == msg.sender
                            && this.guess == guess)
    ensures r.Revert? ==>
              (old(this.state) == this.state && old(this.guess) == this.guess && old(this.player) == this.player && old(this.bet)
                                                                                                                    == this.bet)
    ensures g == 0 || g <= gas - 1
    ensures GInv()
    decreases gas
  {
    if !(this.state == GAME_AVAILABLE && msg.sender != this.operator && msg.sender != this && 0 < msg.value <= msg.sender.balance
         && this.balance >= 0)
    {
      return (if gas >= 1 then gas - 1 else 0), Revert();
    }
    var tg, tr := transfer(msg.sender, this, msg.value, gas);
    if tr.Revert? {
      return (if tg >= 1 then tg - 1 else 0), Revert();
    }
    if tg >= 1 {
      this.state := BET_PLACED;
      this.player := msg.sender;
      this.bet := msg.value;
      this.guess := guess;
      g, r := tg - 1, Success(());
    } else {
      return tg, Revert();
    }
  }

  method decideBet(msg: Msg, secretNumber: int, gas: nat) returns (g: nat, r : Try<()>)
    requires gas >= 1
    requires GInv()
    modifies this, this.operator, this.player
    // ensures this.state == IDLE
    // ensures this.bet == 0
    ensures r.Success? ==> (this.state == IDLE && this.bet == 0 
    &&( this.pot == this.pot + this.bet || this.pot == this.pot - this.bet))
    ensures r.Revert? ==> (this.state == old(this.state) && this.bet == old(this.bet) && this.pot == old(this.pot) 
    && this.player == old(this.player))
    ensures g == 0 || g <= gas - 1
    ensures GInv()
    decreases gas
  {
    if !(this.state == BET_PLACED && msg.sender == this.operator && cryptohash(secretNumber) == this.hashedNumber &&
         msg.sender != this && player != this && this.player.balance >= 0 && 0 < 2 * this.bet <= this.balance &&
         0 < 2 * this.bet <= this.pot)
    {
      return (if gas >= 1 then gas - 1 else 0), Revert();
    }

    var secret: Coin := getCoinFromNumber(secretNumber);
    var tg: nat, tr: Try<()>;
    tg := gas;
    if secret == this.guess {
      // Player wins
      tg, tr := transfer(this, this.player, 2 * this.bet, gas);
      if tr.Revert? {
        return (if tg >= 1 then tg - 1 else 0), Revert();
      }
      if tg >= 1 {
        this.pot := this.pot - this.bet;
        g, r := tg - 1, Success(());
      } else {
        return tg, Revert();
      }
    } else {
      // Operator wins
      this.pot := this.pot + this.bet;
    }
    this.bet := 0;
    this.state := IDLE;
    g, r := (tg - 1), Success(());
  }

  // method externalCall(gas: nat) returns (g: nat, r: Try<()>)
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