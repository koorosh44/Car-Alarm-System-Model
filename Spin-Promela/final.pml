bool armed = false; 
bool key_pressed = false; 
bool door_open = false;
bool window_open = false;
bool ignition_on = false;
bool unauthorized_access = false;
bool disarm_command = false;
bool alarm_active = false; // Add this to track if the alarm is active

active proctype Initialization() {
    if
    :: key_pressed && !armed -> 
        armed = true;
        printf("System armed.\n")
    :: else -> skip;
    fi;
}

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

active proctype Detection() {
    do
    :: armed && unauthorized_access ->
        printf("Unauthorized access detected!\n");
        alarm_active = true;
        run AlarmActivation();
    :: else -> skip;
    od;
}

active proctype AlarmActivation() {
    printf("Alarm activated: Siren sound, lights flashing, ignition disabled.\n");
}

active proctype UserIntervention() {
    do
    :: disarm_command && armed ->
        armed = false;
        alarm_active = false;
        printf("System disarmed.\n");
    :: else -> skip;
    od;
}

active proctype TestScenario() {
    key_pressed = true;
    run Initialization();
    disarm_command = true;
    run UserIntervention();
    unauthorized_access = true;
    run Detection();
}

/* LTL Specifications */

// choose one of these properties for checking.

/* 1. The system can only be armed if the key is pressed. */
ltl always_key_pressed_before_armed { [] (!armed || key_pressed) }

/* 2. If unauthorized access is detected while the system is armed, the alarm will be activated. */
ltl unauthorized_access_triggers_alarm { [] (!armed || !unauthorized_access || alarm_active) }

/* 3. If a disarm command is issued, the system will be disarmed. */
ltl disarm_command_effective { [] (disarm_command -> <> !armed) }

/* 4. The alarm should not activate if the system is disarmed. */
ltl no_alarm_when_disarmed { [] (!armed -> !alarm_active) }
