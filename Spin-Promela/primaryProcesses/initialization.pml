bool armed = false; // Indicates if the system is armed
bool key_pressed = false; // Indicates if the key fob button is pressed

active proctype Initialization() {
    if
    :: key_pressed && !armed -> 
        armed = true;
        printf("System armed.\n")
    :: else -> skip;
    fi;
}
