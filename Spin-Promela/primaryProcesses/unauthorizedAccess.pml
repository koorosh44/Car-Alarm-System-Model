bool unauthorized_access = false;

active proctype Detection() {
    do
    :: armed && unauthorized_access ->
        printf("Unauthorized access detected!\n");
        // Trigger alarm
        run AlarmActivation();
    :: else -> skip;
    od;
}

active proctype AlarmActivation() {
    printf("Alarm activated: Siren sound, lights flashing, ignition disabled.\n");
}
