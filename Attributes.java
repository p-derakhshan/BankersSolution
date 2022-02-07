package com.der.bankerssolution;

import java.util.Arrays;
import javax.swing.JOptionPane;

public class Attributes {

    private int resource[]; //total resources vector
    private int claim[][]; //claimed resources matrix (C)
    private int available[]; //available resources vector (V)
    private int alloc[][]; //currently allocated resources matrix (A)
    private int furtherReq[][]; //remaining requests matrix (C-A)
    private boolean pEnable[];//state of each process (ended/running)
    private int ended[]; //ended state for a process (for checking)

    private int n; //number of processes
    private int m; //number of resources

    private String result; //JOptionPane MessageDialog title
    private boolean state; // final result (safe/unsafe)
    private String message; //JOptionPane MessageDialog message

    //cunstructor 
    public Attributes(int resV[], int claimM[][], int procNum, int resNum) {
        this.n = procNum;
        this.m = resNum;
        state = false;
        result = "";
        message = "";

        resource = new int[resNum];
        available = new int[resNum];
        claim = new int[procNum][resNum];
        alloc = new int[procNum][resNum];
        ended = new int[m];
        pEnable = new boolean[n];

        resource = resV;
        for (int i = 0; i < procNum; i++) { //processes
            pEnable[i] = true;
            for (int j = 0; j < resNum; j++) { //resources
                alloc[i][j] = 0;
                claim[i][j] = claimM[i][j];
            }
        }
        for (int j = 0; j < m; j++) {
            available[j] = resV[j];
            ended[j] = 0;
        }
        furtherReq = requestMatrix(claim, alloc);
    }

    //starts the checking process of the class
    public String[] checkSafeState(int pNum, int[] request) {
        printM();
        startAlgorithm(pNum, request);
        //returning string[]
        String[] r = {"false", result, message};
        if (state) {
            r[0] = "true";
        }
        //print in terminal
        printM();
        return r;
    }

    //starts the algorithm for P(pNum) with R(request[]) 
    private void startAlgorithm(int pNum, int[] request) {
        furtherReq = requestMatrix(claim, alloc); //C-A
        int[] processK = rowM(furtherReq, pNum); //C-A[pNum] 
        if (compare(request, processK) || (!pEnable[pNum])) {
            //alloc+req>claim || process has ended
            //doesn't accept the request
            state = false;
            result = "total requests > claimed requests";
            message = "INVALID REQUEST";
            if (!pEnable[pNum]) {
                for (int j = 0; j < m; j++) {
                    furtherReq[pNum][j] = 0;
                }
                result = "this process has already ended";
            }
        } else if (compare(request, available)) {
            //req>available
            //doesn't accept the request
            state = false;
            result = "requests > available resources";
            message = "PROCESS SUSPENDED";
        } else {
            // request is valid
            boolean check = simulate(pNum, request);
        }
    }

    //simulates next state after granting the request and checks if it's safe
    private boolean simulate(int row, int[] request) {
        //creates a temporary state
        int[][] currentAlloc = new int[n][m];
        int[] currentAvailable = new int[n];
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < m; j++) {
                currentAlloc[i][j] = alloc[i][j];
                if (i == row) {
                    currentAlloc[row][j] += request[j];
                }
            }
        }
        //applies the request on the temporary state
        for (int j = 0; j < m; j++) {
            currentAvailable[j] = (available[j] - request[j]);
        }
        int[][] currentFurtherReq = requestMatrix(claim, currentAlloc);
        //checks if the request ends the process
        int[] pFur = rowM(currentFurtherReq, row);
        if (Arrays.equals(pFur, ended)) {
            for (int j = 0; j < m; j++) {
                currentAvailable[j] += currentAlloc[row][j];
                currentAlloc[row][j] = 0;
            }
        }
        //checks if it leads to deadlock or not
        boolean safe = isSafe(currentAlloc, currentFurtherReq, currentAvailable);
        if (safe) {
            //finalizes the request on the main state
            for (int j = 0; j < m; j++) {
                alloc[row][j] += request[j];
                available[j] -= request[j];
                furtherReq[row][j] -= request[j];
            }
            //checks if the request ends the process
            pFur = rowM(furtherReq, row);
            if (Arrays.equals(pFur, ended)) {
                pEnable[row] = false;
                for (int j = 0; j < m; j++) {
                    available[j] += alloc[row][j];
                    System.out.print("r" + j + ", ");
                    alloc[row][j] = 0;
                }

                JOptionPane.showMessageDialog(null, "Process " + (row + 1) + " has ended",
                        "Process Ended", JOptionPane.INFORMATION_MESSAGE);
                //ends the process
            }
            message = "REQUEST GRANTED";
            result = "Operation Done Successfully";
            state = true;
            return true;
        } else {
            //returns to the previous state without the any changes
            //doesn't accept the request
            message = "REQUEST DENIED";
            state = false;
            result = "This Operation Can Lead to Deadlock";
            return false;
        }
    }

    //checks if the current state will lead to deadlock
    private boolean isSafe(int[][] currentAlloc, int[][] currentFurtherReq, int[] currentAvail) {
        boolean found;
        int[] prossK;
        //checks if all processes can end without deadlock
        for (int k = 0; k < n; k++) {
            prossK = rowM(currentFurtherReq, k); //C-A[P(k)]
            if (noReqV(prossK)) {
                // no further request from the current process (ended)
                continue;
            } else {
                //claim[k][*]-alloc[k][*]<=currentAvail -->found
                found = !compare(prossK, currentAvail);
                if (found) {
                    //process k can end using currently available resources
                    //frees allocated resources of k
                    for (int j = 0; j < m; j++) {
                        currentAvail[j] += currentAlloc[k][j];
                    }
                    //ends process k
                    currentAlloc = endProcess(currentAlloc, k);
                    currentFurtherReq = endProcess(currentFurtherReq, k);
                    //check the new state
                    k = -1;
                }
                //if not found, tries the next process
            }
        }
        //if all processes can end without causing deadlock, the state is safe
        return noReqM(currentFurtherReq); // rest == null
    }

    //returns further request matrix = C-A
    private int[][] requestMatrix(int[][] claim, int[][] alloc) {
        int[][] r = new int[n][m];
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < m; j++) {
                r[i][j] = claim[i][j] - alloc[i][j];
            }
        }
        return r;
    }

    //returns vector [row] of matrix a[][] ( a[row,*] - b[row,*] )
    private int[] rowM(int[][] a, int row) {
        int[] r = new int[m];
        for (int j = 0; j < m; j++) {
            r[j] = a[row][j];
        }
        return r;
    }

    //checks if a[] is bigger than b[] ( a > b --> true)
    private boolean compare(int[] a, int[] b) {
        for (int i = 0; i < m; i++) {
            if (a[i] > b[i]) {
                return true;
            }
        }
        return false;
    }

    //checks if all values of matrix[][] are 0 (no more requests for all processes)
    //matrix[*][*] = 0 --> true
    private boolean noReqM(int[][] fur) {
        int[] r = new int[m];
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < m; j++) {
                r[j] = fur[i][j];
                if (!noReqV(r)) {
                    return false;
                }
            }
        }
        return true;
    }

    //checks if all values of vector[] are 0 (no more requests for the process)
    //vector[*] = 0 --> true 
    private boolean noReqV(int[] fur) {
        for (int i = 0; i < m; i++) {
            if (fur[i] > 0) {
                return false;
            }
        }
        return true;
    }

    //matrix[k][*] = 0
    private int[][] endProcess(int[][] a, int k) {
        for (int j = 0; j < m; j++) {
            a[k][j] = 0;
        }
        return a;
    }

    //returns currently allocated resources matrix (C)
    public int[][] getAllocM() {
        return alloc;
    }

    //returns further requests matrix (C-A)
    public int[][] getFurM() {
        return furtherReq;
    }

    //returns currently available resources vector
    public int[] getAvail() {
        return available;
    }

    //prints in terminal
    public void printM() {
        System.out.print("\nAllocation Matrix:");
        System.out.print("                 Further Requests Matrix:");
        System.out.println("                   Available Vector:");
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < m; j++) {
                System.out.print(alloc[i][j] + " ");
            }
            System.out.print("                             ");
            for (int j = 0; j < m; j++) {
                System.out.print(furtherReq[i][j] + " ");
            }
            if (i == 0) {
                System.out.print("                                     ");
                for (int j = 0; j < m; j++) {
                    System.out.print(available[j] + " ");
                }
            }
            System.out.println("");
        }
        System.out.println("");
    }
    //test case
    /* public Attributes() {
        n = 4;
        m = 3;
        result = ""; //final result
        claim = new int[][]{{3, 2, 2}, {6, 1, 3}, {3, 1, 4}, {4, 2, 2}};
        alloc = new int[][]{{1, 0, 0}, {5, 1, 1}, {2, 1, 1}, {0, 0, 2}};
        available = new int[]{1, 1, 2};
        resource = available;
    }*/
}
