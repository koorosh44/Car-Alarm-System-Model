bool disarm_command = false;

active proctype UserIntervention() {
    do
    :: disarm_command && armed ->
        armed = false;
        printf("System disarmed.\n");
    :: else -> skip;
    od;
}
