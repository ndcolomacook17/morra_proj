'reach 0.1';

const [ isFingers, ZERO, ONE, TWO, THREE, FOUR, FIVE ] = makeEnum(6);
const [ isGuess, ZEROG, ONEG, TWOG, THREEG, FOURG, FIVEG, SIXG, SEVENG, EIGHTG, NINEG, TENG ] = makeEnum(11);
const [ isOutcome, B_WINS, DRAW, A_WINS ] = makeEnum(3);

const winner = (fingersA, fingersB, guessA, guessB) => { 
  if ( guessA == guessB ) 
   {
    const myoutcome = DRAW; 
    return myoutcome;
} else {
  if ( ((fingersA + fingersB) == guessA ) ) {
    const myoutcome = A_WINS;
    return myoutcome;
  } 
    else {
      if (  ((fingersA + fingersB) == guessB)) {
        const myoutcome = B_WINS;
        return myoutcome;
    } 
      else {
        const myoutcome = DRAW; 
        return myoutcome;
      }
    
    }
  }
};

// All key asserts
assert(winner(ZERO,TWO,ZEROG,TWOG)== B_WINS);
assert(winner(TWO,ZERO,TWOG,ZEROG)== A_WINS);
assert(winner(ZERO,ONE,ZEROG,TWOG)== DRAW);
assert(winner(ONE,ONE,ONEG,ONEG)== DRAW);


forall(UInt, fingersA =>
  forall(UInt, fingersB =>
    forall(UInt, guessA =>
      forall(UInt, guessB =>
    assert(isOutcome(winner(fingersA, fingersB, guessA, guessB)))))));


forall(UInt, (fingerA) =>
  forall(UInt, (fingerB) =>       
    forall(UInt, (guess) =>
      assert(winner(fingerA, fingerB, guess, guess) == DRAW))));    


const Player =
      { ...hasRandom,
        getFingers: Fun([], UInt),
        getGuess: Fun([UInt], UInt),
        seeWinning: Fun([UInt], Null),
        seeOutcome: Fun([UInt], Null) ,
        informTimeout: Fun([], Null)
       };

const Alice =
        { ...Player,
          wager: UInt, 
          ...hasConsoleLogger
        };

const Bob =
        { ...Player,
          acceptWager: Fun([UInt], Null),
          ...hasConsoleLogger           
        };
const DEADLINE = 30; 

export const main =
  Reach.App(
    {},
    [Participant('Alice', Alice), Participant('Bob', Bob)],
    (A, B) => {
        const informTimeout = () => {
          each([A, B], () => {
            interact.informTimeout(); }); };
      A.only(() => {
        const wager = declassify(interact.wager); });
      A.publish(wager)
        .pay(wager);
      commit();   

      B.only(() => {
        interact.acceptWager(wager); });
      B.pay(wager)
        .timeout(relativeTime(DEADLINE), () => closeTo(A, informTimeout));

      var outcome = DRAW;      
      invariant(balance() == 2 * wager && isOutcome(outcome) );
      
      while ( outcome == DRAW ) {
        commit();
        A.only(() => {    
          const _fingersA = interact.getFingers();
          const _guessA = interact.getGuess(_fingersA);  
          
          interact.log(_fingersA);  
          
          const [_commitA, _saltA] = makeCommitment(interact, _fingersA);
          const commitA = declassify(_commitA);        
          const [_guessCommitA, _guessSaltA] = makeCommitment(interact, _guessA);
          const guessCommitA = declassify(_guessCommitA);   
      });
     
        A.publish(commitA)
          .timeout(relativeTime(DEADLINE), () => closeTo(B, informTimeout));
        commit();    

        A.publish(guessCommitA)
          .timeout(relativeTime(DEADLINE), () => closeTo(B, informTimeout));
          ;
        commit();
        
        unknowable(B, A(_fingersA, _saltA));
        unknowable(B, A(_guessA, _guessSaltA));

        B.only(() => {

          const _fingersB = interact.getFingers();
          const _guessB = interact.getGuess(_fingersB);
          const fingersB = declassify(_fingersB); 
          const guessB = declassify(_guessB);  

          });

        B.publish(fingersB)
          .timeout(relativeTime(DEADLINE), () => closeTo(A, informTimeout));
        commit();
        B.publish(guessB)
          .timeout(relativeTime(DEADLINE), () => closeTo(A, informTimeout));
          ;
        
        commit();
        A.only(() => {
          const [saltA, fingersA] = declassify([_saltA, _fingersA]); 
          const [guessSaltA, guessA] = declassify([_guessSaltA, _guessA]); 

        });
        A.publish(saltA, fingersA)
          .timeout(relativeTime(DEADLINE), () => closeTo(B, informTimeout));
        checkCommitment(commitA, saltA, fingersA);
        commit();

        A.publish(guessSaltA, guessA)
        .timeout(relativeTime(DEADLINE), () => closeTo(B, informTimeout));
        checkCommitment(guessCommitA, guessSaltA, guessA);

        commit();
      
        A.only(() => {        
          const WinningNumber = fingersA + fingersB;
          interact.seeWinning(WinningNumber);
        });
     
        A.publish(WinningNumber)
        .timeout(relativeTime(DEADLINE), () => closeTo(A, informTimeout));

        outcome = winner(fingersA, fingersB, guessA, guessB);
        continue; 
       
      }

      assert(outcome == A_WINS || outcome == B_WINS);
      transfer(2 * wager).to(outcome == A_WINS ? A : B);
      commit();
 
      each([A, B], () => {
        interact.seeOutcome(outcome); })
      exit(); });