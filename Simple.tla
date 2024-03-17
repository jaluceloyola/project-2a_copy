-------------------------- MODULE Simple  --------------------------

EXTENDS Integers

CONSTANTS Floors

VARIABLES 
    currentFloor,
    MOVING,
    NOTMOVING,
    requestQueue,
    opTime                          \* operation time
    minFloor
    maxFloor

Max == 1000

Init == v = 0
    /\ currentFloor = 1
    /\ cabinDoor = CLOSED
    /\ floor1Door = CLOSED
    /\ floor2Door = CLOSED
    /\ floor3Door = CLOSED
    /\ floor4Door = CLOSED
    /\ requestQueue = << >>            \* start w/ blank queue -- 
    /\ opTime = 0

Tick == 
    /\ running = ON
    /\ timeRemaining' = timeRemaining - 1
    /\ timeRemaining' >= 0
    /\ IF timeRemaining' = 0 THEN running' = OFF ELSE UNCHANGED << running >>
    /\ UNCHANGED << door >>
    \*  \/  /\ v' = v + 1     \*move up 1
    \*      /\ v' <= Max      \* until reach max
    \*  \/  /\ v >= Max    
    \*      /\ UNCHANGED <<v>>

OpenDoor ==
    /\ door' = OPEN
    /\ UNCHANGED << running, timeRemaining >>

CloseDoor ==
    /\ door' = CLOSED
    /\ UNCHANGED << running, timeRemaining >>

floor1Request == \* add floor to Q FIFO
    /\ requestQueue' = << 1 >> \o requestQueue

floor2Request == \* add floor to Q
    /\ requestQueue' = << 2 >> \o requestQueue

floor3Request == \* add floor to Q
    /\ requestQueue' = << 3 >> \o requestQueue

floor4Request == \* add floor to Q
    /\ requestQueue' = << 4 >> \o requestQueue

checkQueue ==
    IF currentFloor = Head(requestQueue) THEN
    /\ requestQueue' = Tail(requestQueue)

moveUp ==
    IF Head(requestQueue) <= currentFloor THEN UNCHANGED currentFloor ELSE  
    \/  /\ currentFloor' = currentFloor + 1     \*move up 1
        /\ currentFloor' <= maxFloor      \* until reach max
    \/  /\ currentFloor >= MaxFloor    


moveDown ==
    IF Head(requestQueue) >= currentFloor THEN UNCHANGED currentFloor ELSE  
    \/  /\ currentFloor' = currentFloor - 1     \*move down 1
        /\ currentFloor' <= minFloor      \* until reach max
    \/  /\ currentFloor >= minFloor  

TypeOK == \*v \in 0..Max
    /\ elevatorPosition \* need to have a variable like doorstate to reference \in DoorState 
    /\ cabin  
    /\ requestQueue \* TODO
    /\ operation

Next == 
    \/ moveUp /\ Tick
    \/ moveDown /\ Tick
    \/ floor1Request /\ Tick
    \/ floor2Request /\ Tick
    \/ floor3Request /\ Tick
    \/ floor4Request /\ Tick
    \/ checkQueue /\ Tick

\*  \/  /\ v' = v + 1     \*move up 1
\*      /\ v' <= Max      \* until reach max
\*  \/  /\ v >= Max    
\*      /\ UNCHANGED <<v>>

Spec == Init /\ [][Next]_v

Safety == v % 2 = 0

LivenessConditions == TRUE

RunsUntilDoneOrInterrupted == TRUE

====