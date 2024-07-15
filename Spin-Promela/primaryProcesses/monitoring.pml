bool door_open = false;
bool window_open = false;
bool ignition_on = false;

active proctype Monitoring() {
    do
    :: armed -> 
        if
        :: door_open -> printf("Door open detected.\n");
        :: window_open -> printf("Window open detected.\n");
        :: ignition_on -> printf("Ignition on detected.\n");
        :: else -> skip;
        fi;
    :: else -> skip;
    od;
}
