/* This program is an hybrid adaptation of the popular metaheuristics Particle Swarm Optimization Algorithm (PSO)
*  for solving the Post Enrolment Course Timetabling problem (PE - CTT) in universities and other higher level
*  educational Institutes.
*  The study is based in the rules and regulations proposed by The 2nd International Timetabling Competition (ITC 2007)
*  that took place in year 2007 and on the input data published by this competition.
*  
*                          Ioannis A. Mantoudis (EAP code: 73134)
*                          E - mail: gmantoudis@hol.gr
*/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <string.h>
#include <malloc.h>

// File handle for the input file that contains the data to be read 
FILE *fh;  
// File handles for reading ... 
FILE *fh1, *fh2; // They are for handling the two txt files, that they will contain the best timetable by class and by teacher respectively
// File handle for the txt file that contains the results analysis 
FILE *fh3; 
// File handle for the txt file that contains the fitness of the function during the evolution of the algorithm 
FILE *fh4;
/* File handle for storing an index that will be updated by adding 1 every time the *fh4 file is created.
*  This way, the file *fh4 will have a suffix that will distinguish the different versions (copies) of file *fh4, 
*  opened by the current application when it is run in parallel. 
*/
FILE *fh5; 


#define ROOMS_NUMBER1 30
#define EVENTS_NUMBER1 50
#define HCW 1

/* Definition of the cost of the algorithm parameters
*  Not yet Created!!!
*/

#define UNBLOCKING_FACTOR1 10
#define FALSE 0
#define TRUE !FALSE

double escape;
int unblock;

int static counterInvalidSwapsAccepted;

#define swapInt(x, y, tmp) {tmp = x; x = y; y = tmp}

#define PARTICLES 50 // The number of particles.
#define ITERATIONS 10000 // The number of iterations (evolution generations) of the algorithm).
#define REFINEMENT_STEPS 500000 // The number of refinement iterations (for the refinement state).
#define INF 1000000000 // This is a large whole number that represents the worst possible fitness value in a minimization problem.

int timesOk;
/* The above array is an Integer array for storing numbers from 0 to Events_number - 1 
* which represents if an event with that number is scheduled to a room at a specific timeslot, for each
* of the particles. In other words, they are candidate best timetbles.
*/
int x[PARTICLES][ROOMS_NUMBER1][45];

int personalBest[PARTICLES][ROOMS_NUMBER1][45]; // Array for recording the personal best of each particle in every iteration.

int globalBest[ROOMS_NUMBER1][45]; // Array for recording the global best solution (best Timetable).

/* The next 3 arrays are needed for the evolution of the algorithm. */
int s[ROOMS_NUMBER1][45];
int v[ROOMS_NUMBER1][45];
int w[ROOMS_NUMBER1][45];

int globalBestFitness; // The global best fitness for each iteration. Ideal case is that globalBestFitness = 0 after algorith termination
int fitnessXLbest[PARTICLES]; // Array for recording the best fitness of each particle, achived by the algorithm up to a certain iteration point

int pIndex; // Index for storing the order of the particle with the best fitness up to this point

int fitnessX; // Variable that contains the fitness of a particle at a given iteration
int initialFitnessX;

time_t pure_time, beginTime, endTime, currentTime; // They are used for counting the elapsed time
double executionTime, lastUpdatingTime;		// Variables for storing the execution time of the algorithm.


/******************************             FUNCTION PROTOTYPES               ******************************/

int  initializeRandomness(int seed); // It is used for initializing random seeds for the rand() function
int random(int lower, int upper); // It produces a random INTEGER number in the range of [lower, upper]
void bubbleSort(int table[][2], int size); // Bubble sort routine for sorting in descending order
void swapTableElements(int table[][2],  int point1, int point2); // Swaps two rows of a 2-column table
int copyMatrices(int begin, int end, int b[][45], int a[][45], int dimension); // Copies the elements of Matrix A to Matrix B
int initializeParticles(int numberOfRooms, int numberOfParticles, int numberOfEvents); // Initialize particles with -1
int swap(int a[][45], int room1,  int timeslot1, int timeslot2); // Performs elementary swap for a room (row) between two timeslots (columns) of particle x[p]
int swapTwoColumns(int a[][45], int timeslot1, int timeslot2, int roomsNumber); // Performs all the swaps between two timeslots without probability
int checkSingleRoomEmptyPeriods(int begin, int end, int a[][45], int roomNumber,  int showResults); // It returns the number of empty periods tha a room may have
int swapIsValid(int begin, int end, int a[][45], int room1, int numberOfRooms, int numberOfEvents, int numberOfStudents, int timeslot1, int timeslot2, int sAvail[numberOfStudents][45]); 
int acceptSwapWithProbability(int begin, int end, int a[][45], int room1, int numberOfRooms, int numberOfEvents, int numberOfStudents, int timeslot1, int timeslot2, int sAvail[numberOfStudents][45]); // Swaps 2 timeslots with a certain probability regarding Hard or Soft constraint violations
int performSwapWithProbability(int begin, int end, int p, int a[][45], int timeslot1, int timeslot2, int numberOfRooms, int numberOfEvents, int numberOfStudents, int times, int sAvail[numberOfStudents][45]);
int calculateSoftConstraintFitness(int a[][45], int numberOfRooms, int numberOfEvents, int numberOfStudents, int sAvail[numberOfStudents][45]); // Calculates the penalty of the 3 Soft Constraint Violations of particle a[][45]
int distToFeasibility(int a[][45], int numberOfRooms, int numberOfEvents, int numberOfStudents, int attendsMtrx[numberOfStudents][numberOfEvents]); // Calculates Distance to Feasibility 

/******************************            END OF FUNCTION PROTOTYPES               ******************************/


/******************************             HELPER FUNCTIONS                   ******************************/

int initializeRandomness(int seed)
{
    int seed1;
	time_t *tp;
	tp = NULL;
	if(seed == -1)
		seed1 = time(tp);
	else
	    seed1 = seed;  
	srand(seed1);
	return seed1;
}

int random(int lower, int upper)
{
    return lower + rand()%(upper - lower + 1);
}

void bubbleSort(int table[][2], int size)
{
     int p = 0; // Number of passes in Bubble Sort routine
     int done = FALSE; // Records if the array has been sorted
     int a, temp0, temp1;
     
     while(done)
     {
        done = TRUE; // If the array is already sorted
        /* Sort the array by swapping elements */
        for(a = size - 1; a > p; a--)
        {
              if(table[a][0] > table[a-1][0])
              {
                   temp0 = table[a-1][0];
                   temp1 = table[a-1][1];
                   
                   table[a-1][0] = table[a][0];
				   table[a-1][1] = table[a][1];
				   
				   table[a][0] = temp0;
				   table[a][1] = temp1;

                   done = FALSE; // The array is still not sorted
               }
         }
         p++;
     }            
}

void swapTableElements(int table[][2],  int point1, int point2)
{
    int temp0, temp1;
	
    if(point1 == point2) 
         return;
	if(table[point1][0] == table[point2][0]) 
         return;
	
    temp0 = table[point1][0];
	temp1 = table[point1][1];

	table[point1][0] = table[point2][0];
	table[point1][1] = table[point2][1];

	table[point2][0] = temp0;
	table[point2][1] = temp1; 
}

int copyMatrices(int begin, int end, int b[][45], int a[][45], int dimension)
{
	int i, j;
	for(i = 0; i < dimension; i++)
		for(j = begin; j < end; j++)
			b[i][j] = a[i][j];
	return 1;
}

int swap(int a[][45], int room1,  int timeslot1, int timeslot2)
{
    int temp;
    temp = a[room1][timeslot1];
    a[room1][timeslot1] = a[room1][timeslot2];
    a[room1][timeslot2] = temp;
	return 1;
}

int swapTwoColumns(int a[][45], int timeslot1, int timeslot2, int roomsNumber)
{
    int row;
	for(row = 0; row < roomsNumber; row++)
		swap(a,  row, timeslot1, timeslot2);
	return 1; 
}


/******************************             END OF HELPER FUNCTIONS               ******************************/

/******************************             ALGORITHM FUNCTIONS                   ******************************/

int initializeParticles(int numberOfRooms, int numberOfParticles, int numberOfEvents)
{
    int p, room1, timeslot;
    
    for(p = 0; p < numberOfParticles; p++)
    {
          for(room1 = 0; room1 < numberOfRooms; room1++)
          {
               for(timeslot = 0; timeslot < 45; timeslot++)
               {
                    x[p][room1][timeslot] = -1; // Initialize every particle with -1
               }
          }
    }
    return 1;      
}

int checkSingleRoomEmptyPeriods(int begin, int end, int a[][45], int roomNumber,  int showResults)
{
    int i, j, k, t, k1;
    int numberOfGaps = 0;
    int start = 0;
    
    //For any day of the week
    for(start = begin; start < end; start = start + 7)
    {
        // For any of the 9 timeslots of a day      
        for(t = start; t < start + 9; t++)
        {
             if (a[roomNumber][t] == -1 && t != 8 && t != 17 && t != 26 && t != 35 && t != 44)
             {
                 numberOfGaps++;
             }
        }
    }
    return numberOfGaps;  
}

int acceptSwapWithProbability(int begin, int end, int a[][45], int room1, int numberOfRooms, int numberOfEvents, int numberOfStudents, int timeslot1, int timeslot2, int sAvail[numberOfStudents][45])
{
	int ok ;

	double r1;
	ok = swapIsValid(begin, end, a, room1, numberOfRooms, numberOfEvents, numberOfStudents, timeslot1, timeslot2, sAvail);
	if(ok == 1) // which means that no hard constraint is violated and the fitness concerning the soft constraint is smaller.
	   return 1;

  	else if(ok == -1) //which means there are no Hard Constraints violations
    {
	   	r1 = rand() / ((double)RAND_MAX + 1.0);

		//if(r1 <= 2.0 / 101.0)
		if(r1 <= 0.5)
        {
			counterInvalidSwapsAccepted++;
			return 1;
		}
		return -1;
	}
    else if(ok == -2)  // No hard constraint is violated but the swap yields bigger fitness if performed, 
    {                  // concerning The Soft Constraints violations 
		r1 = rand() / ((double)RAND_MAX + 1.0);

		//if(r1 <= 2.0 / 101.0){
		if(r1 <= 0.005)
        {

			counterInvalidSwapsAccepted++;
			return 1;  
		}

		return -1;
	}
	return -1;

}

int swapIsValid(int begin, int end, int a[][45], int room1, int numberOfRooms, int numberOfEvents, int numberOfStudents, int timeslot1, int timeslot2, int sAvail[numberOfStudents][45])
{
    /* This function plays an important part in the previous performSwapWithProbability function and return 
    *  1 if the swap between 2 timeslots of the particle is valid due to Hard Constraint violations.
    *  If none of the hard constraints is violated, it then checks for Soft Constraint violations and 
    *  If the swap is going to yield worse Soft Constraint fitness, then it is marked as Invalid and returns 2.
    */
    
    int ok1, ok2;
    int f1, f2;
    
    if(a[room1][timeslot1] == -1 && a[room1][timeslot2] == -1) return 1;  //swap is valid.
    
    /* We now check if the room1 has more gaps if the swap is performed than if it is not.
	* If the gaps are more, then obviously the  swap is not valid.
	*/

	ok1 = checkSingleRoomEmptyPeriods(begin, end, a, room1, 0);
	//perform temporary swap.
	swap(a, room1, timeslot1, timeslot2);
	// Now, we check again room1 for gaps.
	ok2 = checkSingleRoomEmptyPeriods(begin, end, a, room1, 0);

	if(ok2 > ok1 )
    {
		/* The swap is invalid because it causes more clashes(empty spaces).
		*  So, the function restores the initial state and return -1.
		*/
		swap(a, room1, timeslot1, timeslot2);
		return -1;

	}
    else
    {
		//restore initial state , because the swap is valid and there we will have a swap.
		swap(a, room1, timeslot1, timeslot2);
	}
	
	/* Up to this point none of the Hard Constraints is violated, because of the swap.
    *  The next step is to check if the fitness concerning only the Soft Constraints is bigger, if a swap is performed. 
    *  In that case the function will return -2 , because the performed swap is invalid. 
    *  Otherwise the function will return 1, because the swap is valid.
    */
    
   // Now we can calculate the Soft Constraint Fitness
   f1 = calculateSoftConstraintFitness(a, numberOfRooms, numberOfEvents, numberOfStudents, sAvail);
   // Making a temporary swap.
   swap(a, room1, timeslot1, timeslot2);
   
   f2 = calculateSoftConstraintFitness(a, numberOfRooms, numberOfEvents, numberOfStudents, sAvail);
   if(f2 > f1)
   {
	    // Restoring initial state.
		swap(a, room1, timeslot1, timeslot2);
		return -2;
	}
    else
    {
	    // Restoring initial state.
		swap(a, room1, timeslot1, timeslot2);
	}

	return 1;  //swap is valid.
}

int performSwapWithProbability(int begin, int end, int p, int a[][45], int timeslot1, int timeslot2, int numberOfRooms, int numberOfEvents, int numberOfStudents, int times, int sAvail[numberOfStudents][45])
{
     /* This function performs all the swaps between two columns(columnslots) for all rooms, if they are valid.
     *  If a swap is invalid it is accepted with a probability.
     */
     
     int i, ok;
     for(i = 0; i < numberOfRooms; i++)
     {
		//printf("I am processing class number %d\n", i);
		ok = acceptSwapWithProbability(begin, end, a, i, numberOfRooms, numberOfEvents, numberOfStudents, timeslot1, timeslot2, sAvail);
        
        if(ok == 1) // The swap must be performed
        {
             swap(a, i, timeslot1, timeslot2);
        }
        
     }
     
     return 1;
}    
int calculateSoftConstraintFitness(int a[][45], int numberOfRooms, int numberOfEvents, int numberOfStudents, int sAvail[numberOfStudents][45])
{
    // Tranformation of the particle a[][45] to 1 - D array
    int i, j, f, k, n, g, d, t;
    int eR = numberOfRooms * 45; 
    int eRooms[eR];
    int evSlots[numberOfEvents], evRooms[numberOfEvents];
    
    for (i = 0; i < numberOfRooms; i++)
    {
        for(j = 0; j < 45; j++)
        {
              f = i * 45 + j;
              eRooms[f] = a[i][j];
        }
    }
    
    // Creation of eventSlots array from particle a[][45] - Shows the timeslot that an event has been assigned
    for (k = 0; k < numberOfEvents; k++)
    {
        i = 0;
        int find = 0;
        while(i < (numberOfRooms * 45))
        {
             if(eRooms[i] == k)
             {
                  find =1;
                  evSlots[k] = i;
             }   
             i++;
        }     
        if(find == 0)
        {
             evSlots[k] = -1;
        }    
    }
    
    for (k = 0; k < numberOfEvents; k++)
    {
        i = 0;
        while((i < (numberOfRooms * 45)) && (eRooms[i] != k))
        {
             i++;
        }
                              
        if(eRooms[i] == k)
        {
             for(n = 1; n <= numberOfRooms; n++)
             {
                   if(i < (n * 45))
                   {
                        evRooms[k] = n;
                        break;
                   }     
             }    
        }
        else
             evRooms[k] = -1;    
    }
    
    // Soft Constraint 1 evaluation - Checking for events in the last timeslot of a day
    int endOfDay = 0;
    
    for (g = 0; g < numberOfStudents; g++)
    {
        if(sAvail[8][g] == 0)
        {
            endOfDay++;
        }
        if(sAvail[17][g] == 0)
        {
            endOfDay++;
        }
        if(sAvail[26][g] == 0)
        {
            endOfDay++;
        }
        if(sAvail[35][g] == 0)
        {
            endOfDay++;
        }
        if(sAvail[44][g] == 0)
        {
            endOfDay++;
        }
    }
    
    // Soft Constraint 2 evaluation - Checking for consecutive events
    int longIntensive = 0;
    
    for (g = 0; g < numberOfStudents; g++)
    {
        for (d = 0; d < 5; d++)
        {
           int count = 0;
           for (t = 0; t < 9; t++)
           {
               int slot = d * 9 + t;
               if(sAvail[slot][g] == 0)
                   count++;
               else
                   count = 0;
             
               if(count >= 3)
               {
                 //printf("\n\nStudent %d has a set of three events up to slot %2d\n", g, slot);
                 longIntensive++;
               }
           }
        }
    }
    
    // Soft Constraint 3 evaluation - Checking for single events
    int singleEvent = 0;
   
    for (g = 0; g < numberOfStudents; g++)
    {
        for (d = 0; d < 5; d++)
        {
            int count = 0;
            int wrongslot = -1;
            for (t = 0; t < 9; t++)
            {
                int slot = d * 9 + t;
                if(sAvail[slot][g] == 0)
                {
                    count++;
                    wrongslot = slot;
                }
            }
            if(count == 1)
            {
                //printf("\n\nStudent %3d has an event int timeslot %3d and this event is an isolated event\n", g, wrongslot);
                singleEvent++;
            }
        }
    }
    return(endOfDay + longIntensive + singleEvent);       
}

int distToFeasibility(int a[][45], int numberOfRooms, int numberOfEvents, int numberOfStudents, int attendsMtrx[numberOfStudents][numberOfEvents])
{
    int i, j, f, k, n, u;
    int unplaced = 0;
    int eR = numberOfRooms * 45; 
    int eRooms[eR];
    int evSlots[numberOfEvents], evRooms[numberOfEvents];
    int dstToFeasibility = 0;
    
    for (i = 0; i < numberOfRooms; i++)
    {
        for(j = 0; j < 45; j++)
        {
              f = i * 45 + j;
              eRooms[f] = a[i][j];
        }
    }
    
    // Creation of eventSlots array from particle a[][45] - Shows the timeslot that an event has been assigned
    for (k = 0; k < numberOfEvents; k++)
    {
        i = 0;
        int find = 0;
        while(i < numberOfRooms * 45)
        {
             if(eRooms[i] == k)
             {
                  find = 1;
                  evSlots[k] = i;
             }
             i++;
        }     
        if(find == 0)
        {     
             evSlots[k] = -1;
        }    
    }
    
    for (k = 0; k < numberOfEvents; k++)
    {
        i = 0;
        while((i < (numberOfRooms * 45)) && (eRooms[i] != k))
        {
             i++;
        }
                              
        if(eRooms[i] == k)
        {
             for(n = 1; n <= numberOfRooms; n++)
             {
                   if(i < (n * 45))
                   {
                        evRooms[k] = n;
                        break;
                   }     
             }    
        }
        else
             evRooms[k] = -1;    
    }
    
    for (i = 0; i < numberOfEvents;i++)
    {    
         if(evSlots[i] == -1)
         {
              unplaced++;
              for (u = 0;u <numberOfStudents; u++)
              {
                  if(attendsMtrx[i][u]==1)
                  { 
                       dstToFeasibility++;
                  }
              }     
         }              
    }
    return(dstToFeasibility);     
}


/******************************             END OF ALGORITHM FUNCTIONS               ******************************/

/******************************             MAIN FUNCTION                           ******************************/

int main()
{

    int nbrRooms, nbrStudents, nbrEvents, nbrFeatures;
    int unplaced = 0;
    int distanceToFeasibility = 0;
    int i, j, t, w, e, g, d, f, k, n, p;
    int ti, ia, ib, ic, id, ga;
    int eventa, eventb;
    int orderClashes, longIntensive, singleEvent, endOfDay;
    int studentClashes, roomClashes;
    int unsuitableRooms, unsuitableSlots, bdroom;
    int done;
    int ch;
    int times1, byChanceTermination;
    int timeslot1, timeslot2, timeslot3;
    
    double diff;
    double fitnessXBeforeEntering;
    
    char nameOfDataFile[15];
    char fitnessEvolutionFile[150];
    
	int storeParticle[nbrRooms][45]; // This matrix is for storing the structure of particle before perturbation procedure

	int storeParticleA[nbrRooms][45]; // This matrix is for storing the structure of particle before entering the while loop perturbation procedure
     
    system("cls");
    puts("******************************************************************************");
    printf("\n                    H Y B R I D  P S O  A L G O R I T M H \n\n");
    printf("                           for the solution of the \n\n");
    printf("P O S T  E N R O L M E N T  C O U R S E  T I M E T A B L I N G  P R O B L E M\n\n");
    printf("\n\n                    Ioannis A. Mantoudis (EAP code: 73134)\n");
    printf("\n                          E - mail: gmantoudis@hol.gr\n");
    puts("******************************************************************************"); 
    
    
    
    printf("\n\nPlease enter the name of txt dataset (dataset1 - dataset4).\n\n");
	scanf("%s", nameOfDataFile);
	strcat(nameOfDataFile, ".txt");
	
    if((fh = fopen(nameOfDataFile, "r")) == NULL)
    {
		printf("\nError opening file %s. \n", nameOfDataFile);
		printf("\nProgram ending.\n");
		exit(0);
	}
	
	fscanf(fh," %d %d %d %d",&nbrEvents, &nbrRooms, &nbrFeatures, &nbrStudents); 

	//	classes_no = atoi(number_of_classes1);
    int eR[450]; // nbrRooms(10)  * 45 timeslots = 450
    int roomSizes[nbrRooms];
    int eventRooms[nbrEvents];
    int eventSlots[nbrEvents];
    int eventTypes[nbrEvents];
    
    int roomFeatures[nbrRooms][nbrFeatures];
    int eventFeatures[nbrEvents][nbrFeatures];
	int attends[nbrStudents][nbrEvents];
	int eventEvent[nbrEvents][nbrEvents];
	int eventTimeslots[nbrEvents][45];
	int studentAvailability[nbrStudents][45];
	
    // read roomsizes
    for (i = 0; i < nbrRooms; i++)
        fscanf(fh, "%2d", &roomSizes[i]);
        
    // read attends matrix     
    for (i = 0; i < nbrStudents; i++)
    {
        for (t = 0; t < nbrEvents; t++)
        {
            fscanf(fh, "%d", &attends[i][t]);
        }
    }  
     
    // read roomfeatures
    for (i = 0; i < nbrRooms; i++)
    {
        for (t = 0; t < nbrFeatures; t++)
        {
            fscanf(fh, "%d", &roomFeatures[i][t]);
        }
    }
    
    // read eventfeatures    
    for (i = 0; i < nbrEvents; i++)
    {
        for (t = 0; t < nbrFeatures; t++)
        {
            fscanf(fh, "%d", &eventFeatures[t][i]);
        }
    }
    
    // read availability
    for (i = 0; i < nbrEvents; i++)
    {
        for (t = 0; t < 45; t++)
        {
            fscanf(fh, "%d", &eventTimeslots[i][t]);
        }
    }
    
    // read event - event constraints
    for (eventb = 0; eventb < nbrEvents; eventb++)
    {
        for (eventa = 0; eventa < nbrEvents; eventa++)
        {
            fscanf(fh, "%d", &eventEvent[eventb][eventa]);
        }
    }
    
    
    
    // Hard coded creation of a solution particle P for testing purposes
    int P[10][45] = {
        -1, 0, 1, 2, 3, -1, -1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
        -1, -1, -1, 45, -1, -1, -1, -1, 48, 49, 50, 51, 52, 53, 54, 55, 59, -1, 266, 56, 58, -1, -1, 60, 61, 62, 63, -1, 202, 203, 204, 205, -1, 67, 68, -1, 69, -1, -1, -1, 64, 65, 66, -1, -1,
        -1, -1, -1, 366, 367, 368, 369,-1, -1, 370, -1, -1, 371, 372, 373, 374, 375, 376, 377, 378, 379, 390, 391, 392, 393, 394, 395, 396, 397, 398, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 99,
        98, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,-1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,-1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,-1, -1, -1, -1, -1, -1, -1, -1,
        70, 71, 72, 73, 74, 75, 76, 77, 78, 79, -1, -1, -1, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, -1, -1, -1,-1, -1, -1, -1, -1, -1, -1, -1,
        80, 81, 82, 83, 84, 85, 86, 87, 88, 89, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,-1, -1, -1, -1, -1, -1, -1, -1,
        210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, 101, 102, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,-1, -1, -1, -1, -1, -1, -1, -1
        };
    
    // Tranformation of the particle P to 1 - D array
    for (i = 0; i < nbrRooms; i++)
    {
        for(j = 0; j < 45; j++)
        {
              f = i * 45 + j;
              eR[f] = P[i][j];
              // printf("%d\t", eR[f]); for testing purposes
        }
    }
    
    // Creation of eventSlots array from particle P - Shows the timeslot that an event has been assigned
    printf("\n\n\n");
    for (k = 0; k < nbrEvents; k++)
    {
        i = 0;
        while((i < nbrRooms * 45) && (eR[i] != k))
        {
             i++;
        }     
        if(eR[i] == k)
             eventSlots[k] = i;
        else
             eventSlots[k] = -1;
        
        
    }
    
    printf("\n\n");
    // Testing eventSlots matrix (tested OK)
   /*
    for (k = 0; k < nbrEvents; k++)
        printf("%d\t", eventSlots[k]);
   
    */
    // Creation of eventRooms array from particle P - Shows the room that an event has been assigned
    for (k = 0; k < nbrEvents; k++)
    {
        i = 0;
        while((i < (nbrRooms * 45)) && (eR[i] != k))
        {
             i++;
        }
                              
        
        if(eR[i] == k)
        {
             for(n =1; n <= nbrRooms; n++)
             {
                   if(i < (n * 45))
                   {
                        eventRooms[k] = n;
                        break;
                   }     
             }    
        }
        else
             eventRooms[k] = -1;    
    }
    // Testing eventRooms matrix (tested OK)
    /*
    printf("\n\n");
    for (k = 0; k < nbrEvents; k++)
        printf("%d\t", eventRooms[k]);
    */
    
    // Calculation of unplaced events and The 'Distance to Feasibility' metricd
    for (i = 0; i < nbrEvents;i++)
    {
         //if(eventSlots[i] == -1)
             //printf("\nEvent %d does not have a timeslot assigned \n\n", i);
         
         //if(eventRooms[i] == -1)
             //printf("Event %d does not have a room assigned \n\n", i);
         
         if(eventSlots[i] == -1)
         {
              unplaced++;
              for (ga = 0;ga <nbrStudents; ga++)
              {
                  if(attends[i][ga]==1) 
                       distanceToFeasibility++;
              }     
         }              
    } 
    
    // Hard Constraint 2 evaluation - Checking for proper room capacities and missing features
    // Hard Constraint 4 evaluation - Checking events for available timeslots
    unsuitableRooms = 0;
    unsuitableSlots = 0;
    
    for (e = 0; e < nbrEvents; e++)
    {
        int size = 0;
        int bdroom = 0;
        for (g = 0; g < nbrStudents; g++)
        {
            if(attends[e][g] == 1)
            { 
                size++;
                
            }
            
        }        
        
        if((eventRooms[e] != -1) && (roomSizes[eventRooms[e]] < size))
        {
            //printf("\n\nEvent %d requires a room of size %d\n\n", e, size);
            //printf("It has been assigned a room of size %d\n\n", roomSizes[eventRooms[e]]);
            bdroom = 1;
        }
 
        for (f = 0; f < nbrFeatures; f++)
        {
            if(eventRooms[e] != -1)
            {
                if(eventFeatures[e][f] && !roomFeatures[eventRooms[e]][f])
                {
                    //printf("Event %d requires feature %d\n", e, f);
                    //printf("The event has been assigned room %d that does not have feature %d\n\n", eventRooms[e], f);
                    bdroom = 1;
                }
                
                if(bdroom == 1)
                     unsuitableRooms++;    
            }
        }
        if(eventSlots[e] != -1)
        {
             if(eventTimeslots[eventSlots[e]][e] == 0) // event in unavailable timeslot
             {
                  //printf("Event %d has been assigned timeslot %d which is not available\n\n", e, eventSlots[e]);
                  unsuitableSlots++;
             }
        }       
    }
    
    // Hard Constraint 5 evaluation - Checking precedence of events (event - event constraints)
    orderClashes = 0;
    
    for (eventa = 0; eventa < nbrEvents; eventa++)
    {
        for (eventb = 0; eventb < nbrEvents; eventb++)
        {
            if(eventEvent[eventa][eventb] == 1)
            {
                 if((eventSlots[eventa]!= -1) && (eventSlots[eventb]!= -1))
                 {
                      if(eventSlots[eventa] <= eventSlots[eventb])
                      {
                            //printf("\n\nEvent %d in slot # %d must take place after event %d in slot # %d but does not\n", eventa, eventSlots[eventa], eventb, eventSlots[eventb]);
                            orderClashes++;
                      }      
                 }
            }
         }
    }
    
    // Hard Constraint 1 evaluation - Checking for students that attend events in the same timeslot
    // Hard Constraint 3 evaluation - Checking for occupuncy (1 event per room) 
    studentClashes = 0;
    roomClashes = 0;
    
    for (i = 0; i < nbrStudents; i++)
    {
        for (e = 0; e < 45; e++)
        {
            studentAvailability[i][e] = 1;
        }
    }
    
    for (g = 0; g < nbrStudents; g++)
    {
        for (e = 0; e < nbrEvents; e++)
        {
            for (f = 0; f < e; f++)
            {
                if((eventSlots[e] != -1) && (eventSlots[f] != -1) && (eventTimeslots[e][g] ==1) && (eventTimeslots[f][g] ==1) && (eventSlots[e] == eventSlots[f]))
                {
                     studentClashes++;
                }
                
            }
            
            if((eventSlots[e] != -1) && eventTimeslots[e][g])
            {
                 studentAvailability[eventSlots[e]][g] = 0;
            }
        }
    }
    
    for (e = 0; e < nbrEvents; e++)
    {
        for (f = 0; f < e; f++)
        {
            if((eventSlots[e] != -1) && (eventSlots[f] != -1) && (eventRooms[e] != -1) && (eventRooms[f] != -1) && (eventSlots[e] == eventSlots[f]) && (eventRooms[e] == eventRooms[f]))
            {
                 //printf("Event %d and event %d both occur in timeslot %d and room %d \n", e, f, eventSlots[e], eventRooms[e]);
                 roomClashes++;
            }
        }
    }
        
    // Soft Constraint 1 evaluation - Checking for events in the last timeslot of a day
    endOfDay = 0;
    
    for (g = 0; g < nbrStudents; g++)
    {
        if(studentAvailability[8][g] == 0)
        {
            //printf("Student %d has an event in timeslot 8 which is the last slot in Day 1 (Monday)\n\n", g);
            endOfDay++;
        }
        if(studentAvailability[17][g] == 0)
        {
            //printf("Student %d has an event in timeslot 17 which is the last in Day 2 (Tuesday)\n\n", g);
            endOfDay++;
        }
        if(studentAvailability[26][g] == 0)
        {
            //printf("Student %d has an event in timeslot 26 which is the last in Day 3 (Wednesday)\n\n", g);
            endOfDay++;
        }
        if(studentAvailability[35][g] == 0)
        {
            //printf("Student %d has an event in timeslot 35 which is the last in Day 4 (Thursday)\n\n", g);
            endOfDay++;
        }
        if(studentAvailability[44][g] == 0)
        {
            //printf("Student %d has an event in timeslot 44 which is the last in Day 5 (Friday)\n\n", g);
            endOfDay++;
        }
    }
        
    // Soft Constraint 2 evaluation - Checking for consecutive events
    longIntensive = 0;
    
    for (g = 0; g < nbrStudents; g++)
    {
        for (d = 0; d < 5; d++)
        {
           int count = 0;
           for (t = 0; t < 9; t++)
           {
               int slot = d * 9 + t;
               if(studentAvailability[slot][g] == 0)
                   count++;
               else
                   count = 0;
             
               if(count >= 3)
               {
                 //printf("\n\nStudent %d has a set of three events up to slot %2d\n", g, slot);
                 longIntensive++;
               }
           }
        }
    }
        
    // Soft Constraint 3 evaluation - Checking for single events
    singleEvent = 0;
   
    for (g = 0; g < nbrStudents; g++)
    {
        for (d = 0; d < 5; d++)
        {
            int count = 0;
            int wrongslot = -1;
            for (t = 0; t < 9; t++)
            {
                int slot = d * 9 + t;
                if(studentAvailability[slot][g] == 0)
                {
                    count++;
                    wrongslot = slot;
                }
            }
            if(count == 1)
            {
                //printf("\n\nStudent %3d has an event int timeslot %3d and this event is an isolated event\n", g, wrongslot);
                singleEvent++;
            }
        }
    }    
        
    done = FALSE;    
    while(!done)
    {
         printf("\n\nMAIN MENU\n\n");
         printf("0 - Display Basic DataFile Information\n");
         printf("1 - Review of Hard Constraint 1\n");
         printf("2 - Review of Hard Constraint 2\n");
         printf("3 - Review of Hard Constraint 3\n");
         printf("4 - Review of Hard Constraint 4\n");
         printf("5 - Review of Hard Constraint 5\n");
         printf("6 - Review of Soft Constraint 1\n");
         printf("7 - Review of Soft Constraint 2\n");
         printf("8 - Review of Soft Constraint 3\n");
         printf("9 - Review of the evaluation and fitness of the solution (particle)\n");
         printf("10 - End Evaluation - Proceed to PSO Algorithm\n");
         printf("\nSelect a choice and press Enter: ");
         
         scanf("%d", &ch);
         switch(ch)
         {
             case(0):
                 printf("\n\nIn %s there are %d events, %d Rooms, %d features and %d students\n", nameOfDataFile, nbrEvents, nbrRooms, nbrFeatures, nbrStudents);
                 printf("\n\nRoomsizes\n\n");
                 printf("In file %s there are %d rooms with the following capacities\n\n", nameOfDataFile, nbrRooms);
                 for (i = 0; i <nbrRooms; i++)
                     printf("%2d\t", roomSizes[i]);
                 printf("\n\n\n");
                 break;
             case(1):
                 printf("\n\n*******************************************\n\n");
                 printf("Hard Constraint 1 evaluation analysis\n\n");
                 printf("*******************************************\n\n");
                 
                 studentClashes = 0;
                 
                 for (g = 0; g < nbrStudents; g++)
                 {
                     for (e = 0; e < nbrEvents; e++)
                     {
                         for (f = 0; f < e; f++)
                         {
                              if((eventSlots[e] != -1) && (eventSlots[f] != -1) && (eventTimeslots[e][g] ==1) && (eventTimeslots[f][g] ==1) && (eventSlots[e] == eventSlots[f]))
                                   printf("Student %d has to attend both event %d and event %d in Timeslot %d\n\n", g, e, f, eventSlots[e]);
                         }
                     }                     
                 }
                 printf("\nNumber of Students Clashes: %d\n\n", studentClashes);
                 break;
             case(2):
                 printf("\n\n*******************************************\n\n");
                 printf("Hard Constraint 2 evaluation analysis\n\n");
                 printf("*******************************************\n\n");
                 
                 unsuitableRooms = 0;
                 
                 for (e = 0; e < nbrEvents; e++)
                 {
                     int size = 0;
                     int bdroom = 0;
                     for (g = 0; g < nbrStudents; g++)
                     {
                         if(attends[e][g] == 1)
                         { 
                              size++;
                         }
                     }
                     
                     printf("\n%d event has % d students\n", e, size);
                     if((eventRooms[e] != -1) && (roomSizes[eventRooms[e]] < size))
                     {
                          printf("\n\nEvent %d requires a room of size %d\n\n", e, size);
                          printf("It has been assigned a room of size %d\n\n", roomSizes[eventRooms[e]]);
                          bdroom = 1;
                     }
                     for (f = 0; f < nbrFeatures; f++)
                     {
                         if(eventRooms[e] != -1)
                         {
                              if(eventFeatures[e][f] && !roomFeatures[eventRooms[e]][f])
                              {
                                   printf("Event %d requires feature %d\n", e, f);
                                   printf("The event has been assigned room %d that does not have feature %d\n\n", eventRooms[e], f);
                                   bdroom = 1;
                              }
                         }
                                         
                         if(bdroom == 1)
                              unsuitableRooms++;
                     }   
                 }    
                  printf("\nNumber of Unsuitable Rooms = %d\n\n", unsuitableRooms);
                 break;
             case(3):
                 printf("\n\n*******************************************\n\n");
                 printf("Hard Constraint 3 evaluation analysis\n\n");
                 printf("*******************************************\n\n");
                 
                 roomClashes = 0;
                 
                 for (e = 0; e < nbrEvents; e++)
                 {
                     for (f = 0; f < e; f++)
                     {
                          if((eventSlots[e] != -1) && (eventSlots[f] != -1) && (eventRooms[e] != -1) && (eventRooms[f] != -1) && (eventSlots[e] == eventSlots[f]) && (eventRooms[e] == eventRooms[f]))
                          {
                               printf("Event %d and event %d both occur in timeslot %d and room %d \n", e, f, eventSlots[e], eventRooms[e]);
                               roomClashes++;
                          }
                     }
                 }
                 printf("Number of Room Clashes: %d\n\n", roomClashes);
                 break;        
             case(4):
                 printf("\n\n*************************************\n\n");
                 printf("Hard Constraint 4 evaluation analysis\n\n");
                 printf("*************************************\n");
                 
                 unsuitableSlots = 0;
                 for (e = 0; e < nbrEvents; e++)
                 {
                     if(eventSlots[e] != -1)
                     {
                         if(eventTimeslots[eventSlots[e]][e] == 0) // event in unavailable timeslot
                         {
                              printf("\nEvent %d has been assigned timeslot %d which is not available\n\n", e, eventSlots[e]);
                              unsuitableSlots++;
                         }
                     }
                 }
                 printf("\nNumber of Unsuitable timeslots = %d\n\n", unsuitableSlots);
                 break;  
             case(5):
                 printf("\n\n*************************************\n\n");
                 printf("Hard Constraint 5 evaluation analysis\n\n");
                 printf("*************************************\n");
                 
                 for (eventa = 0; eventa < nbrEvents; eventa++)
                 {
                     for (eventb = 0; eventb < nbrEvents; eventb++)
                     {
                         if(eventEvent[eventa][eventb] == 1)
                         {
                              if((eventSlots[eventa]!= -1) && (eventSlots[eventb]!= -1))
                              {
                                   if(eventSlots[eventa] <= eventSlots[eventb])
                                   {
                                        printf("\n\nEvent %d in slot # %d must take place after event %d in slot # %d but does not\n", eventa, eventSlots[eventa], eventb, eventSlots[eventb]);
                                        orderClashes++;
                                   }      
                              }
                         }
                     }
                 }
                 break;    
             case(6):
                 printf("\n\n*******************************************\n\n");
                 printf("Soft Constraint 1 evaluation analysis\n\n");
                 printf("*******************************************\n\n");
                 
                 endOfDay = 0;
                 
                 for (g = 0; g < nbrStudents; g++)
                 {
                     if(studentAvailability[8][g] == 0)
                     {
                          printf("Student %d has an event in timeslot 8 which is the last slot in Day 1 (Monday)\n\n", g);
                          endOfDay++;
                     }
                     if(studentAvailability[17][g] == 0)
                     {
                          printf("Student %d has an event in timeslot 17 which is the last in Day 2 (Tuesday)\n\n", g);
                          endOfDay++;
                     }
                     if(studentAvailability[26][g] == 0)
                     {
                          printf("Student %d has an event in timeslot 26 which is the last in Day 3 (Wednesday)\n\n", g);
                          endOfDay++;
                     }
                     if(studentAvailability[35][g] == 0)
                     {
                          printf("Student %d has an event in timeslot 35 which is the last in Day 4 (Thursday)\n\n", g);
                          endOfDay++;
                     }
                     if(studentAvailability[44][g] == 0)
                     {
                          printf("Student %d has an event in timeslot 44 which is the last in Day 5 (Friday)\n\n", g);
                          endOfDay++;
                     }
                 }
                 printf("\nPenalty for students having events in the last timeslot of a day = %d\n\n", endOfDay);
                 break;
             case(7):
                 printf("\n\n*******************************************\n\n");
                 printf("Soft Constraint 2 evaluation analysis\n\n");
                 printf("*******************************************\n\n");
                 
                 longIntensive = 0;
                 
                 for (g = 0; g < nbrStudents; g++)
                 {
                     for (d = 0; d < 5; d++)
                     {
                         int count = 0;
                         for (t = 0; t < 9; t++)
                         {
                             int slot = d * 9 + t;
                             if(studentAvailability[slot][g] == 0)
                                  count++;
                             else
                                  count = 0;
             
                             if(count >= 3)
                             {
                                  printf("\nStudent %d has a set of three events up to slot %2d\n", g, slot);
                                  longIntensive++;
                             }
                         }
                     }
                 }
                 printf("\nPenalty for students having three or more events in a row = %d\n\n", longIntensive);
                 break;
             case(8):
                 printf("\n\n*******************************************\n\n");
                 printf("Soft Constraint 3 evaluation analysis\n\n");
                 printf("*******************************************\n\n");
                 
                 singleEvent = 0;
                 
                 for (g = 0; g < nbrStudents; g++)
                 {
                     for (d = 0; d < 5; d++)
                     {
                         int count = 0;
                         int wrongslot = -1;
                         for (t = 0; t < 9; t++)
                         {
                             int slot = d * 9 + t;
                             if(studentAvailability[slot][g] == 0)
                             {
                                  count++;
                                  wrongslot = slot;
                             }
                         }
                     
                         if(count == 1)
                         {
                              printf("\n\nStudent %3d has an event int timeslot %3d and this event is an isolated event\n", g, wrongslot);
                              singleEvent++;
                         }
                     }
                 }    
                 printf("\n\nSingle Events = %d", singleEvent);
                 break;                
             case(9):
                 // Review of the evaluation and fitness of the Particle
                  printf("\n\n************************************************************\n\n");
                  printf("General Review of the evaluation and Fitness of the Particle\n\n");
                  printf("************************************************************\n\n"); 
                  printf("Number of Unsuitable rooms = %d\n\n", unsuitableRooms);
                  printf("Number of Unsuitable timeslots = %d\n\n", unsuitableSlots);                  
                  printf("Number of Ordering Issues = %d\n\n", orderClashes);
                  printf("Number of Student Clashes = %d\n\n", studentClashes);
                  printf("Number of Room Clashes = %d\n\n", roomClashes);
                  printf("Number of Unplaced events = %d\n\n", unplaced);
    
                  printf("Penalty for students having three or more events in a row = %d\n\n", longIntensive);
                  printf("Penalty for students having single events on a day = %d\n\n", singleEvent);
                  printf("Penalty for students having events in the last timeslot of a day = %d\n\n", endOfDay);
                  printf("\n\nDistance to Feasibility = %d\n\n", distanceToFeasibility);
                  printf("Total Soft Constraint Penalty = %d\n\n", longIntensive + singleEvent + endOfDay);     
                 break;
             case(10):
                 printf("\nProceeding to Hybrid PSO Algorithm\n");
                 done = TRUE;
                 break;
             default:
                 printf("\nWrong Selection! Try again\n\n");
                 break;
          }
    }
    
    printf("\n\nData entry completed from file %s \n", nameOfDataFile);
    printf("\nThe program will now proceed to construct the best weekly timetable.\n");
    
    /******************* Initializing Randomness with user seed ********************/
    int seed;
	printf("\nPlease enter your own seed for the Random Number generator. Enter -1 for system seed.\n");
	scanf("%d", &seed);

	seed = initializeRandomness(seed);
	printf("The seed you enter is : %d ", seed);
	
	// begin_time = clock();
    
	// Initializing 50 particles to -1
    initializeParticles(nbrRooms, PARTICLES, nbrEvents);
	printf("\nThe Particles have been initialized.\n");
	printf("\nProgram is running. Please wait...\n");
    
    //initializing the best fitness of each particle to worst possible value (value INF)
	for(p = 0; p < PARTICLES; p++)
		fitnessXLbest[p] = INF;
	
	//initializing the global best fitness to worst possible value (value INF)
	globalBestFitness = INF;

	strcpy(fitnessEvolutionFile, "Fitness Evolution");

	strcpy(fitnessEvolutionFile, strcat(fitnessEvolutionFile, ".txt"));

	fh4 = fopen(fitnessEvolutionFile, "w");
	fprintf(fh4, "	Fitness evolution for input file %s\n\n", nameOfDataFile);
    // Testing the Fitness functions - Tested OK
    int fitnessX = 0;
    fitnessX = HCW * distToFeasibility(x[p], nbrRooms, nbrEvents, nbrStudents, attends);
    printf("\nFitness X = %d", fitnessX);
    int fitnessY = 0;
    fitnessY = calculateSoftConstraintFitness(x[p], nbrRooms, nbrEvents, nbrStudents, studentAvailability);
    printf("\nFitness Y = %d", fitnessY);
    
    for(ti = 0; ti < ITERATIONS; ti++)
    {
		//printf("\nCURRENT GENERATION IS %d Fitness is %f Time elapsed is %f\n", times1, global_best_fitness, (double)(clock() - begin_time)/(double)CLOCKS_PER_SEC);
        // Recording in a txt file the fitness of the particle every 20 iterations
		
        if(ti % 20 == 0)
        { 
			if(globalBestFitness == 0)
				fprintf(fh4, "%d %f \n", ti , log10(globalBestFitness + 0.00000000000001));
			else
				fprintf(fh4, "%d %f \n", ti , log10(globalBestFitness));
		}
		
		for(p = 0; p < PARTICLES; p++)
        {
             fitnessX = HCW * distToFeasibility(x[p], nbrRooms, nbrEvents, nbrStudents, attends)+ 
             + calculateSoftConstraintFitness(x[p], nbrRooms, nbrEvents, nbrStudents, studentAvailability);
            
            // Updating the Personal Best table
            if(fitnessX <= fitnessXLbest[p])
            {
					for(k = 0; k < nbrRooms; k++)
					{
						for(j = 0; j < 45; j++)
						{
							personalBest[p][k][j] = x[p][k][j]; //personal best updated.
                        }
                    }    					
                    fitnessXLbest[p] = fitnessX;                 
					
                    if(fitnessX <= globalBestFitness)
                    {
						if(fitnessX < globalBestFitness)
                        {
							lastUpdatingTime = clock();
							timesOk = ti;
							pIndex = p;
						}
						globalBestFitness = fitnessX; // Upadating Global Best table

						for(k = 0; k < nbrRooms; k++)
						{
							for(j = 0; j < 45; j++)
                            {
								globalBest[k][j] = x[p][k][j];
							}
                        }	
					}
             }
                    
             timeslot1 = random(0, 44);
			 timeslot2 = random(0, 44);
			 while(timeslot2 == timeslot1)
			 {
			      timeslot2 = random(0, 44);
             }
			
			 copyMatrices(0, 45, storeParticle, x[p], nbrRooms);

			 initialFitnessX = fitnessX;

			 // Not yet Created - perform_swap_with_probability(there_is_coteaching, 0, 35, diff, p, x[p], timeslot1, timeslot2, classes_no, teachers_no, global_best_fitness, times1, TEPW, IDWT, IDWC);

			 timeslot1 = random(0, 44);

			 // Not yet created - insert_column(there_is_coteaching, 0, 35, p, personal_best[p], x[p], timeslot1,  classes_no, teachers_no, TEPW, IDWT, IDWC);

			 timeslot2 = random(0, 44);

			 // Not yet created - insert_column(there_is_coteaching, 0, 35, p, global_best, x[p], timeslot2,   classes_no, teachers_no, TEPW, IDWT, IDWC);

			 fitnessX = HCW * distToFeasibility(x[p],nbrRooms, nbrEvents, nbrStudents, attends) + calculateSoftConstraintFitness(x[p], nbrRooms, nbrEvents, nbrStudents, studentAvailability);

			 fitnessXBeforeEntering = fitnessX;

			 copyMatrices(0, 45, storeParticleA, x[p], nbrRooms);
			 unblock = 0;
			 byChanceTermination = 0;          
             
        }// End of for(p =0; p < PARTICLES; p++) loop
        if(ti % 100 == 0 )
        {
			double elapsedTime = (double)(clock() - beginTime)/((double)CLOCKS_PER_SEC)/60;
			printf("\nFOr Input file %s the time elapsed  is: %d  mins and %.1f  secs ", nameOfDataFile, (int)floor(elapsedTime), (elapsedTime - floor(elapsedTime))*60);
			printf("\nGeneration %d. Best fitness  up to this point is %f.\n", ti, globalBestFitness);
        }  
        
    
    }// End of for(ti = 0; ti < ITERATIONS; ti++) loop  
    
    double mainAlgorithmTime;
	endTime = clock();
	mainAlgorithmTime = (double)(endTime - beginTime)/((double)CLOCKS_PER_SEC)/60;
    
    printf("\n\n**********************************************************************************************\n\n");
    printf("\nBEST FITNESS BEFORE REFINMENT LOCAL SEARCH PHASE = %D AND IT IS ACHIEVED AT GENERATION %d \n", globalBestFitness, timesOk);

	
	double lastUpdatingTime2 = (double)(lastUpdatingTime - beginTime)/((double)CLOCKS_PER_SEC)/60;

	printf("Best fitness achieved in %d mins and %.1f sec\n", (int)floor(lastUpdatingTime2), (lastUpdatingTime2 - floor(lastUpdatingTime2))*60);

	printf("\nElapsed time of main  algorithm is %d mins and %.1f secs.\n", (int)floor(mainAlgorithmTime), (mainAlgorithmTime - floor(mainAlgorithmTime))*60);
	//display_results(3, there_is_coteaching, 0, 35,  global_best, teachers_no, classes_no, TEPW, IDWT, IDWC);
	
    printf("The seed is : %d\n", seed);
	
    printf("\nEnd of  main algorithm for input file %s.\n", nameOfDataFile);
    printf("\n\n**********************************************************************************************\n\n");


/******************************          BEGIN OF THE LOCAL SEARCH PHASE          ****************************/
                                                                                                  
    return(0);
}

/******************************             END OF MAIN FUNCTION               ******************************/
