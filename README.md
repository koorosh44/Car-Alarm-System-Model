# Car-Alarm-System-Model

## Overview

This project models a simple car alarm system using formal methods in software engineering. The modeling and verification were carried out using two tools: SPIN-Promela and NuSMV. The purpose of this project is to ensure the correctness and reliability of the car alarm system through formal verification.

## Description

The project follows these steps to model and verify the car alarm system:

1. **Initial Explanation**:
   - A natural language description of the car alarm system was created.

2. **Conceptual Design**:
   - Using the mind mapping method, a simple conceptual model was created, outlining the desired features and functionality.

3. **Inputs and Outputs**:
   - The inputs, outputs, and processes involved in a simple car alarm system were identified.

4. **Modeling**:
   - The system was modeled using NuSMV and SPIN-Promela.
   - The models were created based on the formal methods in software engineering.

5. **Verification**:
   - The models were verified using the verification utilities of NuSMV and SPIN.
   - The model will be updated in the future to adjust some properties that need refinement.

## Requirements

- **NuSMV**: A symbolic model checker for formal verification.
- **SPIN**: A tool for verifying the correctness of distributed software models in a rigorous and mostly automated fashion.
- **Draw.io**: For viewing and editing the mind map (optional).

## Usage

### NuSMV

To verify the car alarm system model using NuSMV:

1. Open a terminal.
2. Navigate to the `NuSMV/` directory.
3. Run the NuSMV tool:
   ```sh
   nusmv carAlarm.smv
   ```
4. Check the verification results in `nusmv_verification.txt`.

### SPIN

To verify the car alarm system model using SPIN:

1. Open a terminal.
2. Navigate to the `Spin-Promela/` directory.
3. Compile the Promela model:
   ```sh
   spin -a final.pml
   ```
4. Use a model checker to verify the generated C code:
   ```sh
   gcc -o pan pan.c
   ./pan
   ```
5. Check the verification results in `spin_verification.txt`.

## Authors

- Kourosh Taghadosi


Affiliation: Islamic Azad University, North Tehran Branch, Fromal Methods, Dr.Khanzadi


---
