/*
** Gereralized Land Use Change Model (gluc)
**
** This is primary code for the land use change model.  The model is
** primarily driven by a probability map and a land use map.  For each
** developed cell on the land use map a probability of development is
** calculated and a random number used to determine if the cell develops
** or not.  A feedback mechanism controls the rate of development increasing
** or decreasing the overall probability based on the desired demand.
**
** Note: he model has evolved significantly over the years and a lot cruf
** has accumulated.  It could use a good cleaning.
**
** Copyright (C) 2013 LEAMgroup, Inc. Released under GPL v2.
*/
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <mpi.h>
#include <unistd.h>
#include <errno.h>
#include "leam.h"
#include "bil.h"
#include "GA.h"
#include <time.h>
static char *ID = "$Id: luc.c,v 1.49 2005/02/17 21:40:47 jefft Exp $";

static int betterK = 1;
static int ResModel = 1, ComModel = 1, OSModel = 1;

static float  xllcorner, yllcorner, cellsize;

unsigned char *boundary, *nogrowth, *developable;
unsigned char *slope, *floodzone;
unsigned char *metrobuffer, *growth_trend_map;
static int    nondevelopable_flags;

static float *probmap_res, *probmap_com, *probmap_os;

static void *demandres, *demandcom, *demandos;
static void *nngraph, *nnosgraph;

unsigned char *highway_att, *road_att, *ramp_att, *intersection_att;
unsigned char *allroad_att, *park_att, *forest_att, *water_att;
unsigned char *vacancy_rate, *avg_income, *rental_rate, *no_car, *same_home;
unsigned char *lu_map, *lu, *change, *summary;
unsigned char *nntmp, *nndev, *nnres, *nncom, *nnos, *nnwater;
unsigned char *zoning;

int *cities_att, *employment_att, *subregions;
float *growth_trend;
float *density_res, *density_com, *density_os;
int cell_count_res = 0, cell_count_com = 0, cell_count_os = 0;

static float buffer_rate_in, buffer_rate_out;
static float w_growth_trend_res, w_growth_trend_com;
static float w_growth_trend_os;
static float w_neighbors_res, w_neighbors_com;
static float w_neighbors_os, w_neighbors_water;
static float w_probmap_res, w_probmap_com, w_probmap_os;
static float w_dynamic_res, w_dynamic_com, w_dynamic_os;
static float w_spontaneous_res, w_spontaneous_com, w_spontaneous_os;
static float w_utilities_res, w_utilities_com, w_utilities_os;
static float w_cities_att_res, w_cities_att_com, w_cities_att_os;
static float w_employment_att_res, w_employment_att_com, w_employment_att_os;
static float w_highway_att_res, w_highway_att_com, w_highway_att_os;
static float w_ramp_att_res, w_ramp_att_com, w_ramp_att_os;
static float w_road_att_res, w_road_att_com, w_road_att_os;
static float w_allroad_att_res, w_allroad_att_com, w_allroad_att_os;
static float w_intersection_att_res, w_intersection_att_com,
             w_intersection_att_os;
static float w_forest_att_res, w_forest_att_com, w_forest_att_os;
static float w_water_att_res, w_water_att_com, w_water_att_os;
static float w_slope_res, w_slope_com, w_slope_os;
static float w_vacancy_rate_res, w_vacancy_rate_com, w_vacancy_rate_os;
static float w_avg_income_res, w_avg_income_com, w_avg_income_os;
static float w_rental_rate_res, w_rental_rate_com, w_rental_rate_os;
static float w_no_car_res, w_no_car_com, w_no_car_os;
static float w_same_home_res, w_same_home_com, w_same_home_os;
static float w_zoning_res, w_zoning_com, w_zoning_os;
static float growthrate_res, growthrate_com, growthrate_os;
static float k_factor_res, k_factor_com, k_factor_os;
static float k_coeff_res, k_coeff_com, k_coeff_os;
static int   refzones = 0, *refmap = NULL, *refcounts = NULL;

static float *ranvals;
static float *resprob, *comprob, *osprob;
static float desired_res = 0.0, desired_com = 0.0, desired_os = 0.0;
/* 20170327 - for test the population */
//static float pop1 = 197450.0, pop2 = 210000.0, emp1 = 111000.0, emp2 = 115000.0;
static int pop1 = 0, pop2 = 0, emp1 = 0, emp2 = 0;
/* 20170327 - global for randval */
static float randval_global;
static float current_res = 0.0, current_com = 0.0, current_os = 0.0;
static float delta_res = 20.0, delta_com = 5.0, delta_os = 500.0;
/* 20170407 - manually changed value*/
static float best_prob_res = 0.235, best_prob_com = 0.215, best_prob_os = 0.01;
static float k_min_res, k_min_com, k_min_os;

static float *utilities_res, *utilities_com, *utilities_os, *utilities_tmp;
static float diffusion_rate, diffusion_rate_os;
static int   diffusion_res_flags, diffusion_com_flags, diffusion_os_flags;
static int   diffusion_init_step, diffusion_steps_os;

static float openspace_los;
 
static char *outbuf;
/* 20170327 - global for pop and com */
static int lu_count_res;
static int lu_count_com;

/* 20170331 - pop and com real_dev each round*/
static float real_dev_res;
static float real_dev_com;
/* 20170407 -20170405 - check if print, 1 mean yes, 0 means no */
static int check_print = 1;
static int global_count_res = 0;
static int global_count_com = 0;

/* 20170407 - 20170403 - global P & Values */
static int compute_global_p = 1;
static int glob_elements; /* seems like useless*/
static float global_res_pval = 0.235000; //max = 1924773 for springfields
static float global_com_pval = 0.156030; //max = 1924773 for springfields
static float global_res_p[6000000]; //max = 1924773 for springfields
static float global_com_p[6000000]; //max = 1924773 for springfields
static float global_res_p_total[6000000]; //max = 5264490 for springfields_total
static float global_com_p_total[6000000]; //max = 5264490 for springfields_total
/*20170414 - fp_com, fp_res*/
static float fp_com;
static float fp_res;
 
void quickSort( int[], int, int);
int partition( int[], int, int);

/* data structure - (v)stack? push/pop queue?  */
/* sort from large to small */

/* MPI information */
static int upproc, downproc;
static int *recvcounts, *displacements;

/* Grid infomration */
int gCols, gRows, gElements;
int srow, erow, elements;



/* debugging routine */
static int qcount(unsigned char *ptr, int count, int val, char *label)
{
   int i, total = 0;

   for (i=0; i<count; i+=1)
       if (*(ptr+i) == val) total += 1;

   if (label != NULL)
       fprintf(stderr, "P%d: %s = %d\n", myrank, label, total);

   return total;
}

/* debugging routine */
static float qsum(float *ptr, char *label)
{
   int i;
   float total = 0.0;

   for (i=0; i<elements; i+=1)
       total += *(ptr+i);

   if (label != NULL)
       fprintf(stderr, "P%d: %s = %f\n", myrank, label, total);

   return total;
}

/* debugging routine */
static void reportGridInfo()
{
    fprintf(stderr, "P%d: rows = %d-%d, cols = %d, elements = %d\n", myrank,
            srow, erow, gCols, elements);
}


void setBetterK(int val)
{
   betterK = val;
}


/* setModel allows various aspects of the model (residential,
** commercial, or openspace development) to be turned on or off.
*/

void setModel(SUBMODELS model, int val)
{
   switch (model)  {

   case RES_MODEL:
       ResModel = val;
       break;

   case COM_MODEL:
       ComModel = val;
       break;

   case OS_MODEL:
       ComModel = val;
       break;
   }

   return;
}

/* Configure some parameters to the make it easier to 
** allocate memory for the data grids.
*/
void LUCconfigGrids(int rows, int cols, int *gridrows)
{
    int i;

    //* set the neighboring processor for communication purposes 
    upproc = myrank - 1;
    if (upproc == -1) upproc = MPI_PROC_NULL;
    downproc = myrank + 1;
    if (downproc == nproc) downproc = MPI_PROC_NULL;

    //* set grid information 
    srow = gridrows[myrank];
    erow = gridrows[myrank+1]-1;
    gRows = rows;
    gCols = cols;
    gElements = rows * cols;
    elements = (erow - srow + 1) * cols;
	glob_elements = elements;

    //* create vectors for MPI_Gatherv call 
    recvcounts = (int *)getMem(nproc * sizeof (int), "recvcounts");
    MPI_Gather(&elements, 1, MPI_INT, recvcounts, 1, MPI_INT, 
               0, MPI_COMM_WORLD);
    MPI_Bcast(recvcounts, nproc, MPI_INT, 0, MPI_COMM_WORLD);

    displacements = (int *)getMem(nproc * sizeof (int), "displacements");
    displacements[0] = 0;
    for (i=1; i<nproc; i+=1)
        displacements[i] = displacements[i-1] + recvcounts[i-1];

    if (debug) reportGridInfo();
}


/* Determine which cells are currently developable.
** 
** POSSIBLE_LU_FOR_COM_IND = if LAND_USE = 11 OR LAND_USE = 21 OR 
**    LAND_USE = 22 OR LAND_USE = 23 OR LAND_USE = 24 OR 
**    LAND_USE = 91 OR LAND_USE = 92 OR LAND_USE = 85 then 0 else 1
** POSSIBLE_LU_FOR_OPENSPACE = if LAND_USE = 11 OR LAND_USE = 21 OR 
**    LAND_USE = 22 OR LAND_USE = 23 OR LAND_USE = 24 OR LAND_USE = 91 OR
**    LAND_USE = 92 OR LAND_USE = 85 then 0 else 1
** POSSIBLE_LU_FOR_RES = if LAND_USE = 11 OR LAND_USE = 21 OR 
**    LAND_USE = 22 OR LAND_USE = 23 OR LAND_USE = 24 OR LAND_USE = 91 OR
**    LAND_USE = 92  OR LAND_USE = 85 then 0 else 1
**
** This routine should be probably combine additional
** information from boundary and nogrowth map (others?) to
** simplify the checking for active cells in the calcProb routines
** but we'll leave it this way for now.
**
** We should probably be able flag different landuse types as developable
** i.e. wetlands, ect.  Or even better have probabiliy based on landuse type.
** Recommend we get rid of this routine.
** The switch statement could get replaced with an equation that
** would eliminates all the comparisons for performance.
*/
static void flagDevelopable(unsigned char *dev, unsigned char *luptr, 
                            int count, LU_FLAG flag)
{
    int i;

    for (i=0; i<count; i+=1)  {
        switch (*(luptr+i))  {
        case LU_WATER:
            *(dev+i) = !(WATER_FLAG & flag);
            break;
        case LU_LRES: case LU_HRES:
            *(dev+i) = !(RES_FLAG & flag);
			lu_count_res += 1;
            break;
        case LU_COM:
            *(dev+i) = !(COM_FLAG & flag);
			lu_count_com += 1;
            break;
        case LU_ROAD:
            *(dev+i) = !(ROAD_FLAG & flag);
            break;
        case LU_HWET: case LU_WET:
            *(dev+i) = !(WETLAND_FLAG & flag);
            break;
        case LU_OS:
            *(dev+i) = !(OS_FLAG & flag);
            break;

        default:
            *(dev+i) = 1;

        }
    }
}


void shareGrid(void *dst, int count, MPI_Datatype type)
{
    int size;
    MPI_Request request;
    MPI_Status status;

    if (nproc == 1) return;

    MPI_Type_size(type, &size);

    //* recieve into upside row and send downside row 
    MPI_Irecv(dst-gCols*size, gCols, type, upproc, 19,
              MPI_COMM_WORLD, &request);
    MPI_Send(dst+(count-gCols)*size, gCols, type, downproc, 19, 
             MPI_COMM_WORLD);
    MPI_Wait(&request, &status);

    //* recieve into downside row and send upside row 
    MPI_Irecv(dst+count*size, gCols, type, downproc, 19,
              MPI_COMM_WORLD, &request);
    MPI_Send(dst, gCols, type, upproc, 19, MPI_COMM_WORLD);
    MPI_Wait(&request, &status);
}

/* Set grids to the a known value.  There should be a better way
** of handling this but for now we'll go with it.  It's only used
** when maps that are expected to be available must be turned-off.
*/


static void setGridMapByte(unsigned char *ptr, int count, float v){
    unsigned char x = v;
    int i;
    for (i=0; i<count; i+=1)
        *(ptr+i) = x;
    shareGrid(ptr, count, MPI_UNSIGNED_CHAR);
    return;
}


/* Set grids to the a known value.  There should be a better way
** of handling this but for now we'll go with it.  It's only used
** when maps that are expected to be available must be turned-off.
*/
static void setGridMapInt(int *ptr, int count, float v){
    int x = v;
    int i;
    for (i=0; i<count; i+=1)
        *(ptr+i) = x;
    shareGrid(ptr, count, MPI_INT);
    return;
}

static void setGridMapFloat(float *ptr, int count, float v){
    int i;
    for (i=0; i<count; i+=1)
        *(ptr+i) = v;
    shareGrid(ptr, count, MPI_FLOAT);
    return;
}

/* Copy from src grid buffer to dst grid buffer.
*/
static void copyGridMap(void *dst, void *src, int count, int size){
    memcpy(dst, src, count * size);
    return;
}

static void checkHeader(char *fname){
    int rows, cols, size;
    if (myrank != 0) return;
    BILreadHeader(fname, &rows, &cols, &size);
    if (rows != gRows || cols != gCols)  {
        sprintf(estring, "map %s has wrong dimensions", fname);
        errorExit(estring);
    }
}

/* Initialize grids.  Sufficient space is allocated for all
** elements plus two additional rows (overlaps with neighboring
** processors).  If a file name is given the grid is initialized
** with data from the file otherwise it defaults to 0.
**
** Note: still dependent on global variable 'gCols'.
** Note: hardcoded for bil files...yuck.
*/
static char *initGridMap(char *fname, int count, int typesize)
{
    int seekbyte, passive;
    char *bufptr, *readptr;
    FILE *f;

    if (debug && myrank == 0 && fname != NULL) 
        fprintf(stderr, "initGridMap(fname=%s, count=%d, size=%d\n",
        fname, count, typesize); 

    /* allocate for all the active elements + 2 passive rows */
    bufptr = getMem((count + gCols + gCols) * typesize, fname);

    /* fill the buffer if filename is provided */
    if (fname != NULL)  {

        /* check that all maps have the same dimensions
        ** this is probably something we don't want to
        ** support long-term as we may want to allow 
        ** on-the-fly interpolation.
        */
        checkHeader(fname);

        /* calculate where to begin reading data into buffer,
        ** basically the beginning of the buffer unless rank = 0
        ** in which case will skip the first row of the buffer.
        */
        readptr = bufptr + ((myrank == 0) ? gCols * typesize : 0);

        /* extra number of elements read for passive rows, 
        ** zero if running in single processor mode,
        ** one row if rank is first or last processor
        ** two rows otherwise.
        */
        if (nproc == 1)
            passive = 0;
        else if (myrank == 0 || myrank == nproc-1)
            passive = gCols;
        else
            passive = 2 * gCols;

        /* calculate seek position into file (first passive row)
        */
        seekbyte = (myrank == 0) ? 0 : (srow-1) * gCols * typesize;
        BILreadBuffer(fname, seekbyte, readptr, count+passive, typesize);
    }

    /* always return pointer to active area of buffer (first
    ** non-passive row of the buffer.
    */
    return bufptr + gCols * typesize;
}

static char *initGridMapNull(char *fname, int count, int typesize)
{
    if (fname == NULL)
        return NULL;
    else
        return initGridMap(fname, count, typesize);
}

/* freeGridMap corrects for additional memory originally
** allocated on each buffer to allow the grid to be freed.
** See the return value of initGridMap for a better understanding.
*/
static void freeGridMap(char *bufptr, int typesize)
{
    freeMem(bufptr - gCols * typesize);
}


/* Mask a grid using a landuse map and lu_type flag.  The masked
** grid is returned with corresponding cells intact and all others
** set to zero.


/* LOGICAL OR two grids together. Grids are converted to boolean
** so anything greater than 0 (including nodata values) is assumed
** to be true.
*/
static void orGridMap(unsigned char *dst, unsigned char *m1, 
                      unsigned char *m2, int count){
    int i;
    for (i=0; i<count; i+=1)  {
        dst[i] = (m1[i] > 0) | (m2[i] > 0);
    }
    return;
}

/* Write the grid to the Map2 file.  The filename has a timestamp
** and .m2 extension appended to it.  The generic output buffer
** is used to gather all the results before writing.
**
** fname can be NULL.  This means that no output file is request
** in the SME configuration file.  Specify it using  the M(M,<d>,<fname>) 
** option in the config file.
**
** Note: To simplify writing the file, the root processor
** will do all the work.  There are probably better methods use MPI I/O.
*/
static int writeGridMap(char *fname, int time, char *src, int count, 
        MPI_Datatype type)
{
    int i, typesize, namelen;
    char fstring[1024], typename[MPI_MAX_OBJECT_NAME];
    MPI_Status status;
    char *ptr = outbuf;

    if (fname == NULL) return 1;

    MPI_Type_size(type, &typesize);
    MPI_Type_get_name(type, typename, &namelen);

    if (debug && myrank == 0)
        fprintf(stderr, "writeGridMap(%s, %d, %d, %s, %d)\n", 
                fname, time, count, typename, typesize);

    /* append timestamp and write header file */
    sprintf(fstring, "%s.bil", fname);
    if (myrank == 0)
        BILwriteHeader(fstring, gRows, gCols, typesize, typename,
                       ulx, uly, xdim, ydim );

    /* if running single processor then write buffer and return */
    if (nproc == 1)  {
        BILwriteBuffer(fstring, 0, src, count, typesize);
        return 1;
    }

#ifdef MYGATHER
    if (myrank == 0)  {
        memmove(ptr, src, count * typesize);
        for (i=1; i<nproc; i+=1)  {
            MPI_Recv(ptr+typesize*displacements[i], recvcounts[i], type,
                     i, 22, MPI_COMM_WORLD, &status);
        }
    }
    else  {
        MPI_Send(src, count, type, 0, 22, MPI_COMM_WORLD);
    }
#else
    /* this doesn't seem to work... */
    MPI_Gatherv(src, count, type, ptr, recvcounts+1,
                displacements+1, type, 0, MPI_COMM_WORLD);
#endif

    if (myrank == 0)
        BILwriteBuffer(fstring, 0, outbuf, gElements, typesize);
    return 1;
}

static void ASCwrite(char *fname, int rows, int cols, float xll, float yll,
                     float cellsize, MPI_Datatype type, void *src){
    int i,j;
    double x;
    FILE *f;
    if (debug && myrank == 0)  {
        fprintf(stderr, "ASCwrite to %s\n", fname);
    }

    if ((f = fopen(fname, "w")) == NULL)  {
         errorExit("unable to write ASC file\n");
    }

    fprintf(f, "ncols\t\t%d\n", cols);
    fprintf(f, "nrows\t\t%d\n", rows);
    fprintf(f, "xllcorner\t%f\n", xll);
    fprintf(f, "yllcorner\t%f\n", yll);
    fprintf(f, "cellsize\t%f\n", cellsize);
    fprintf(f, "NODATA_value\t-1\n");

    for (j=0; j<rows; j+=1)  {
        for (i=0; i<cols; i+=1)  {
            x = *((float *)src+j*cols+i);  
            fprintf(f, "%e ", x);
        }
        fprintf(f, "\n");
    }
    return;
}

/* Write Grid Map in the ASC format.
** 
*/
static int writeAscGridMap(char *fname, int time, char *src, int count, 
        MPI_Datatype type){
    int i, typesize;
    char fstring[1024];
    MPI_Status status;
    char *ptr = outbuf;
    if (fname == NULL) return 1;
    if (debug && myrank == 0)
        fprintf(stderr, "writeAscGridMap(%s, %d, %d)\n", 
                fname, time, count);
    MPI_Type_size(type, &typesize);
    sprintf(fstring, "%s.asc", fname);
    //* if running single processor then write write and return 
    if (nproc == 1)  {
        ASCwrite(fstring, gRows, gCols, xllcorner, yllcorner, cellsize, type, src);
        return;
    }
#ifdef MYGATHER
    if (myrank == 0)  {
        memmove(ptr, src, count * typesize);
        for (i=1; i<nproc; i+=1)  {
            MPI_Recv(ptr+typesize*displacements[i], recvcounts[i], type,
                     i, 22, MPI_COMM_WORLD, &status);
        }
    }
    else  {
        MPI_Send(src, count, type, 0, 22, MPI_COMM_WORLD);
    }
#else
    // this doesn't seem to work... 
    MPI_Gatherv(src, count, type, ptr, recvcounts+1,
                displacements+1, type, 0, MPI_COMM_WORLD);
#endif
    if (myrank == 0)
        ASCwrite(fstring, gRows, gCols, xllcorner, yllcorner, cellsize, type, src);
    return 1;
}

 //Initialize the data grids, handle memory allocation 
// and initialization based on SME variables.
void LUCinitGrids(){
    xllcorner = SMEgetFloat("XLLCORNER", 0.0);
    yllcorner = SMEgetFloat("YLLCORNER", 0.0);
    cellsize = SMEgetFloat("CELLSIZE", 30.0);

    boundary = (unsigned char *)initGridMap(
                SMEgetFileName("BOUNDARY_MAP"), elements, 1);
    nogrowth = (unsigned char *)initGridMap(
                SMEgetFileName("NOGROWTH_ZONE_MAP"), elements, 1);
    nondevelopable_flags = SMEgetInt("NONDEVELOPABLE_FLAGS", 
                                     NONDEVELOPABLE_FLAGS);
    floodzone = (unsigned char *)initGridMap(
                SMEgetFileName("FLOODZONE_MAP"), elements, 1);
    orGridMap(nogrowth, nogrowth, floodzone, elements);
    freeGridMap(floodzone, 1);

    demandres = GRAPHgetGraph(SMEgetString("DEMAND_GRAPH_RES",
                                           "Population"));
    fprintf(stderr, "20170317: DEMAND_GRAPH_RES set to %s\n", 
                SMEgetString("DEMAND_GRAPH_RES", "Population"));	
    demandcom = GRAPHgetGraph(SMEgetString("DEMAND_GRAPH_COM",
                                           "Employment"));
    if (demandres == NULL || demandcom == NULL)
        errorExit("missing DEMAND_GRAPH_RES or DEMAND_GRAPH_COM graphs");

	// debug = 0;
    // Get the RES and COM growth graphs
    if (debug && myrank == 0)  {
        fprintf(stderr, "2010-3: DEMAND_GRAPH_RES set to %s\n", 
                SMEgetString("DEMAND_GRAPH_RES", "Population"));
        fprintf(stderr, "2010-3: DEMAND_GRAPH_COM set to %s\n", 
                SMEgetString("DEMAND_GRAPH_COM", "Employment"));
    }

    nngraph = GRAPHgetGraph("NearestNeighbors");
    if (nngraph == NULL)
        errorExit("missing NearestNeighbors graph");

    demandos = GRAPHgetGraph("CellDemandOS");
    nnosgraph = GRAPHgetGraph("NearestNeighborsOS");
    if (nnosgraph == NULL) nnosgraph = nngraph;
    
    // reads the probabilty map if one is specified
    // otherwise probability map will be set to 1.0
    probmap_res = (float *)initGridMap(NULL, elements, sizeof (float));
    setGridMapFloat(probmap_res, elements, 1.0);
    readProbmap(&probmap_res, elements, sizeof (float),
                SMEgetFileName("PROBMAP_RES"), -1);

    probmap_com = (float *)initGridMap(NULL, elements, sizeof (float));
    setGridMapFloat(probmap_com, elements, 1.0);
    readProbmap(&probmap_com, elements, sizeof (float),
                SMEgetFileName("PROBMAP_COM"), -1);


    probmap_os = (float *)initGridMapNull(SMEgetFileName("PROBMAP_OS"),
                           elements, sizeof (float));
    if (probmap_os == NULL)  {
        probmap_os = (float *)initGridMap(NULL, elements, sizeof (float));
        setGridMapFloat(probmap_os, elements, 1.0);
    }

    // load the population density map if one is provided
    // otherwise assume we're working with cells and create a fake
    // density map where every cell is 1
    density_res = (float *)initGridMap(SMEgetFileName("DENSITY_MAP_RES"),
                                       elements, sizeof (float));
    // change 20170125 - 1
    //if (SMEgetFileName("DENSITY_MAP_RES") == NULL)
        setGridMapFloat(density_res, elements, 1.0);

    density_com = (float *)initGridMap(SMEgetFileName("DENSITY_MAP_COM"),
                                       elements, sizeof (float));
    //if (SMEgetFileName("DENSITY_MAP_COM") == NULL)
        setGridMapFloat(density_com, elements, 0.7);


    utilities_res = (float *)initGridMap(
                SMEgetFileName("UTILITIES_RES_MAP"), elements, sizeof (float));
    utilities_com = (float *)initGridMap(
                SMEgetFileName("UTILITIES_COM_MAP"), elements, sizeof (float));
    utilities_os = (float *)initGridMap(
                SMEgetFileName("UTILITIES_OS_MAP"), elements, sizeof (float));
    utilities_tmp = (float *)initGridMap(NULL, elements, sizeof (float));
    diffusion_rate = SMEgetFloat("U_DIFFUSE_RATE", 0.2);
    //test diffusion rate
    diffusion_rate = SMEgetFloat("U_DIFFUSE_RATE", 0.2);
    diffusion_res_flags = SMEgetInt("U_DIFFUSE_RES_FLAGS", RES_FLAG);
    diffusion_com_flags = SMEgetInt("U_DIFFUSE_COM_FLAGS", COM_FLAG);
    diffusion_os_flags = SMEgetInt("U_DIFFUSE_OS_FLAGS", OS_FLAG);
    diffusion_init_step = SMEgetInt("U_DIFFUSE_INITSTEPS", 10);
    diffusion_rate_os = SMEgetFloat("DIFFUSION_RATE_OS", 0.2);
    //test diffusion rate
    diffusion_rate_os = SMEgetFloat("DIFFUSION_RATE_OS", 0.0);
    diffusion_steps_os = SMEgetInt("DIFFUSION_STEPS_OS", 3);

    /* set landuse data */
    lu_map = (unsigned char *)initGridMap(SMEgetFileName("LU_MAP"), 
              elements, 1);

    change = (unsigned char *)initGridMap(NULL, elements, 1);
    summary = (unsigned char *)initGridMap(NULL, elements, 1);
    lu = (unsigned char *)initGridMap(NULL, elements, 1);
    copyGridMap(lu, lu_map, elements, 1);

    /* */
    developable = (unsigned char *)initGridMap(NULL, elements, 1);
    
    /* nearest neighbor grids */
    nntmp = (unsigned char *)initGridMap(NULL, elements, 1);
    nndev = (unsigned char *)initGridMap(NULL, elements, 1);
    nnres = (unsigned char *)initGridMap(NULL, elements, 1);
    nncom = (unsigned char *)initGridMap(NULL, elements, 1);
    nnos = (unsigned char *)initGridMap(NULL, elements, 1);
    nnwater = (unsigned char *)initGridMap(NULL, elements, 1);

    /* probability grids */
    resprob = (float *)initGridMap(NULL, elements, sizeof (float));
    comprob = (float *)initGridMap(NULL, elements, sizeof (float));
    osprob = (float *)initGridMap(NULL, elements, sizeof (float));

    /* reference grid and count array */
    if (SMEgetFileName("REFERENCE_MAP") != NULL) {
        refmap = (int *)initGridMap(SMEgetFileName("REFERENCE_MAP"), 
                                    elements, sizeof (int));
        refzones = spatialMax(refmap, elements) + 1;
        if (SMEgetFileName("REFERENCE_COUNTS") != NULL)  {
            refcounts = (int *)getMem(refzones * sizeof (int),
                         "refcounts array");
            readReferenceCounts(refcounts, refzones, 
                               SMEgetFileName("REFERENCE_COUNTS"));
        }
        else
            refcounts = NULL;
    }

    /* pre-computed random values */
    ranvals = (float *)initGridMap(NULL, elements, sizeof (float));

    /* k factors */
    growthrate_res = SMEgetFloat("RESIDENTIAL_GROWTH_RATE", -1.0);
    growthrate_com = SMEgetFloat("COMMERCIAL_GROWTH_RATE", -1.0);
    growthrate_os = SMEgetFloat("OPENSPACE_GROWTH_RATE", -1.0);
    openspace_los = SMEgetFloat("OPENSPACE_LOS", -1.0);
    k_coeff_res = SMEgetFloat("K_COEFFICIENT_RES", 0.001);
    k_coeff_com = SMEgetFloat("K_COEFFICIENT_COM", 0.001);
    k_coeff_os = SMEgetFloat("K_COEFFICIENT_OPEN", 0.001);
    k_min_res = SMEgetFloat("K_MIN_RES", 0.001);
    k_min_com = SMEgetFloat("K_MIN_COM", 0.001);
    k_min_os = SMEgetFloat("K_MIN_OPEN", 0.001);
    delta_res = SMEgetFloat("DELTA_RES", delta_res);
    delta_com = SMEgetFloat("DELTA_COM", delta_com);
    delta_os = SMEgetFloat("DELTA_OS", delta_os);
    best_prob_res = SMEgetFloat("BEST_PROB_RES", best_prob_res);
    best_prob_com = SMEgetFloat("BEST_PROB_COM", best_prob_com);
    best_prob_os = SMEgetFloat("BEST_PROB_OS", best_prob_os);
    

    /* driver weights */
    w_probmap_res = SMEgetFloat("W_PROBMAP_RES", 0.5);
    w_probmap_com = SMEgetFloat("W_PROBMAP_COM", 0.5);
    w_probmap_os = SMEgetFloat("W_PROBMAP_OS", 1.0);
    w_dynamic_res = SMEgetFloat("W_DYNAMIC_RES", 30.0);
    w_dynamic_com = SMEgetFloat("W_DYNAMIC_COM", 30.0);
    w_dynamic_os = SMEgetFloat("W_DYNAMIC_OS", 10.0);
    w_utilities_res = SMEgetFloat("W_UTILITIES_RES", 1.0);
    w_utilities_com = SMEgetFloat("W_UTILITIES_COM", 1.0);
    w_utilities_os = SMEgetFloat("W_UTILITIES_OS", 1.0);
    w_spontaneous_res = SMEgetFloat("W_RES_SPONTANEOUS", 20.0);
    w_spontaneous_com = SMEgetFloat("W_COM_IND_SPONTANEOUS", 20.0);
    w_spontaneous_os = SMEgetFloat("W_OPENSPACE_SPONTANEOUS", 1.0);
    w_neighbors_res = SMEgetFloat("W_RES_NEIGHBORS", 1);
    w_neighbors_com = SMEgetFloat("W_COM_IND_NEIGHBORS", 1);
    w_neighbors_water = SMEgetFloat("W_OPENSPACE_WATER", 1);
    w_growth_trend_res = SMEgetFloat("W_GROWTH_TRENDS_RES", 1.0);
    w_growth_trend_com = SMEgetFloat("W_GROWTH_TRENDS_COM_IND", 1.0);
    w_growth_trend_os = SMEgetFloat("W_GROWTH_TRENDS_OPENSPACE", 1.0);
    w_cities_att_res = SMEgetFloat("W_CITIES_ATT_RES", 1.0);
    w_cities_att_com = SMEgetFloat("W_CITIES_ATT_COM", 1.0);
    w_cities_att_os = SMEgetFloat("W_CITIES_ATT_OS", 1.0);
    w_employment_att_res = SMEgetFloat("W_EMPLOYMENT_ATT_RES", 1.0);
    w_employment_att_com = SMEgetFloat("W_EMPLOYMENT_ATT_COM", 1.0);
    w_employment_att_os = SMEgetFloat("W_EMPLOYMENT_ATT_OS", 1.0);
    w_highway_att_res = SMEgetFloat("W_HIGHWAY_ATT_RES", 1.0);
    w_highway_att_com = SMEgetFloat("W_HIGHWAY_ATT_COM", 1.0);
    w_highway_att_os = SMEgetFloat("W_HIGHWAY_ATT_OS", 1.0);
    w_ramp_att_res = SMEgetFloat("W_RAMP_ATT_RES", 1.0);
    w_ramp_att_com = SMEgetFloat("W_RAMP_ATT_COM", 1.0);
    w_ramp_att_os = SMEgetFloat("W_RAMP_ATT_OS", 1.0);
    w_road_att_res = SMEgetFloat("W_ROAD_ATT_RES", 1.0);
    w_road_att_com = SMEgetFloat("W_ROAD_ATT_COM", 1.0);
    w_road_att_os = SMEgetFloat("W_ROAD_ATT_OS", 1.0);
    w_allroad_att_res = SMEgetFloat("W_ALLROAD_ATT_RES", 1.0);
    w_allroad_att_com = SMEgetFloat("W_ALLROAD_ATT_COM", 1.0);
    w_allroad_att_os = SMEgetFloat("W_ALLROAD_ATT_OS", 1.0);
    w_intersection_att_res = SMEgetFloat("W_INTERSECTION_ATT_RES", 1.0);
    w_intersection_att_com = SMEgetFloat("W_INTERSECTION_ATT_COM", 1.0);
    w_intersection_att_os = SMEgetFloat("W_INTERSECTION_ATT_OS", 1.0);
    w_forest_att_res = SMEgetFloat("W_FOREST_ATT_RES", 1.0);
    w_forest_att_com = SMEgetFloat("W_FOREST_ATT_COM", 1.0);
    w_forest_att_os = SMEgetFloat("W_FOREST_ATT_OS", 1.0);
    w_water_att_res = SMEgetFloat("W_WATER_ATT_RES", 1.0);
    w_water_att_com = SMEgetFloat("W_WATER_ATT_COM", 1.0);
    w_water_att_os = SMEgetFloat("W_WATER_ATT_OS", 1.0);
    w_slope_res = SMEgetFloat("W_SLOPE_RES", 1.0);
    w_slope_com = SMEgetFloat("W_SLOPE_COM", 1.0);
    w_slope_os = SMEgetFloat("W_SLOPE_OS", 1.0);
    w_vacancy_rate_res = SMEgetFloat("W_VACANCY_RATE_RES", 1.0);
    w_vacancy_rate_com = SMEgetFloat("W_VACANCY_RATE_COM", 1.0);
    w_vacancy_rate_os = SMEgetFloat("W_VACANCY_RATE_OS", 1.0);
    w_avg_income_res = SMEgetFloat("W_AVG_INCOME_RES", 1.0);
    w_avg_income_com = SMEgetFloat("W_AVG_INCOME_COM", 1.0);
    w_avg_income_os = SMEgetFloat("W_AVG_INCOME_OS", 1.0);
    w_rental_rate_res = SMEgetFloat("W_RENTAL_RATE_RES", 1.0);
    w_rental_rate_com = SMEgetFloat("W_RENTAL_RATE_COM", 1.0);
    w_rental_rate_os = SMEgetFloat("W_RENTAL_RATE_OS", 1.0);
    w_no_car_res = SMEgetFloat("W_NO_CAR_RES", 1.0);
    w_no_car_com = SMEgetFloat("W_NO_CAR_COM", 1.0);
    w_no_car_os = SMEgetFloat("W_NO_CAR_OS", 1.0);
    w_same_home_res = SMEgetFloat("W_SAME_HOME_RES", 1.0);
    w_same_home_com = SMEgetFloat("W_SAME_HOME_COM", 1.0);
    w_same_home_os = SMEgetFloat("W_SAME_HOME_OS", 1.0);

    /* default output buffer (big enough for ints/floats) on root only */
    outbuf = initGridMap(NULL, gElements, 4);
}


void resetWeights()
{
    if (SMEgetFileName("GA_ENGINE") == NULL) return;

    if (debug && myrank == 0)
        fprintf(stderr, "GA_ENGINE = %s\n", SMEgetFileName("GA_ENGINE"));

    if (myrank == 0)
        GAinit(SMEgetFileName("GA_ENGINE"));

    //
    // Truely ugly.  Allows weights to be reset before each
    // run.  AND it doesn't work...need to keep the original
    // value in a safe place!
    //
    w_utilities_res = GAgetData("W_UTILITIES_RES", w_utilities_res );
    MPI_Bcast(&w_utilities_res, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_utilities_com = GAgetData("W_UTILITIES_COM", w_utilities_com );
    MPI_Bcast(&w_utilities_com, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_utilities_os = GAgetData("W_UTILITIES_OS", w_utilities_os );
    MPI_Bcast(&w_utilities_os, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_spontaneous_res = GAgetData("W_RES_SPONTANEOUS", w_spontaneous_res );
    MPI_Bcast(&w_spontaneous_res, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_spontaneous_com = GAgetData("W_COM_IND_SPONTANEOUS", w_spontaneous_com );
    MPI_Bcast(&w_spontaneous_com, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_spontaneous_os = GAgetData("W_OPENSPACE_SPONTANEOUS", w_spontaneous_os );
    MPI_Bcast(&w_spontaneous_os, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_neighbors_res = GAgetData("W_RES_NEIGHBORS", w_neighbors_res );
    MPI_Bcast(&w_neighbors_res, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_neighbors_com = GAgetData("W_COM_IND_NEIGHBORS", w_neighbors_com );
    MPI_Bcast(&w_neighbors_com, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_neighbors_water = GAgetData("W_OPENSPACE_WATER", w_neighbors_os );
    MPI_Bcast(&w_neighbors_os, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_growth_trend_res = GAgetData("W_GROWTH_TRENDS_RES", w_growth_trend_res );
    MPI_Bcast(&w_growth_trend_res, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_growth_trend_com = GAgetData("W_GROWTH_TRENDS_COM_IND", w_growth_trend_com );
    MPI_Bcast(&w_growth_trend_com, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_growth_trend_os = GAgetData("W_GROWTH_TRENDS_OPENSPACE", w_growth_trend_os );
    MPI_Bcast(&w_growth_trend_os, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_cities_att_res = GAgetData("W_CITIES_ATT_RES", w_cities_att_res );
    MPI_Bcast(&w_cities_att_res, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_cities_att_com = GAgetData("W_CITIES_ATT_COM", w_cities_att_com );
    MPI_Bcast(&w_cities_att_com, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_cities_att_os = GAgetData("W_CITIES_ATT_OS", w_cities_att_os );
    MPI_Bcast(&w_cities_att_os, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_highway_att_res = GAgetData("W_HIGHWAY_ATT_RES", w_highway_att_res );
    MPI_Bcast(&w_highway_att_res, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_highway_att_com = GAgetData("W_HIGHWAY_ATT_COM", w_highway_att_com );
    MPI_Bcast(&w_highway_att_com, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_highway_att_os = GAgetData("W_HIGHWAY_ATT_OS", w_highway_att_os );
    MPI_Bcast(&w_highway_att_os, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_ramp_att_res = GAgetData("W_RAMP_ATT_RES", w_ramp_att_res );
    MPI_Bcast(&w_ramp_att_res, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_ramp_att_com = GAgetData("W_RAMP_ATT_COM", w_ramp_att_com );
    MPI_Bcast(&w_ramp_att_com, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_ramp_att_os = GAgetData("W_RAMP_ATT_OS", w_ramp_att_os );
    MPI_Bcast(&w_ramp_att_os, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_road_att_res = GAgetData("W_ROAD_ATT_RES", w_road_att_res );
    MPI_Bcast(&w_road_att_res, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_road_att_com = GAgetData("W_ROAD_ATT_COM", w_road_att_com );
    MPI_Bcast(&w_road_att_com, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_road_att_os = GAgetData("W_ROAD_ATT_OS", w_road_att_os );
    MPI_Bcast(&w_road_att_os, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_intersection_att_res = GAgetData("W_INTERSECTION_ATT_RES", w_intersection_att_res );
    MPI_Bcast(&w_intersection_att_res, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_intersection_att_com = GAgetData("W_INTERSECTION_ATT_COM", w_intersection_att_com );
    MPI_Bcast(&w_intersection_att_com, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_intersection_att_os = GAgetData("W_INTERSECTION_ATT_OS", w_intersection_att_os );
    MPI_Bcast(&w_intersection_att_os, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_forest_att_res = GAgetData("W_FOREST_ATT_RES", w_forest_att_res );
    MPI_Bcast(&w_forest_att_res, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_forest_att_com = GAgetData("W_FOREST_ATT_COM", w_forest_att_com );
    MPI_Bcast(&w_forest_att_com, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_forest_att_os = GAgetData("W_FOREST_ATT_OS", w_forest_att_os );
    MPI_Bcast(&w_forest_att_os, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_water_att_res = GAgetData("W_WATER_ATT_RES", w_water_att_res );
    MPI_Bcast(&w_water_att_res, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_water_att_com = GAgetData("W_WATER_ATT_COM", w_water_att_com );
    MPI_Bcast(&w_water_att_com, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_water_att_os = GAgetData("W_WATER_ATT_OS", w_water_att_os );
    MPI_Bcast(&w_water_att_os, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_slope_res = GAgetData("W_SLOPE_RES", w_slope_res );
    MPI_Bcast(&w_slope_res, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_slope_com = GAgetData("W_SLOPE_COM", w_slope_com );
    MPI_Bcast(&w_slope_com, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
    w_slope_os = GAgetData("W_SLOPE_OS", w_slope_os );
    MPI_Bcast(&w_slope_os, 1, MPI_FLOAT, 0, MPI_COMM_WORLD);
}


void LUCresetGrids()
{
    resetWeights();
    copyGridMap(lu, lu_map, elements, 1);
    setGridMapByte(change, elements, 0.0);
    setGridMapByte(summary, elements, 0.0);
    setGridMapFloat(utilities_res, elements, 0.0);
    setGridMapFloat(utilities_com, elements, 0.0);
    setGridMapFloat(utilities_os, elements, 0.0);

    // is this everything? //
}

// seekMinWeight -- produces MORE development by decreasing the
// weight until development is less than demand
// 
// global variables -- ranvals, elemeents

float seekMinWeight(float demand, float best, float *probmap, float *density)
{
    float dev, olddev = -1.0, w = 1.0;
    int count = 0;

    do  {
        w *= 0.1;
        dev = SPATIALfalseDev2(w, best, probmap, density, ranvals, elements);
        if (debug && myrank == 0)
            fprintf(stderr, "seekMinWeight: w = %f, dev = %f\n", w, dev);

        if (dev == olddev)  {
            if (myrank == 0)
                fprintf(stderr, "seekMinWeight: weight changed failed\n");
            //exit(EXIT_INSUFFICIENT);
        }
        else
            olddev = dev;

       // failed to find a bracketing weight
       if (count++ == 10)
           return 0.0;

    }  while (dev > 0.0 && dev > demand);

    return w;
}

// seekMaxWeight -- produces LESS development by increasing the
// weight until development exceeds demand
// 
// global variables -- ranvals, elemeents
float seekMaxWeight(float demand, float best, float *probmap, float *density)
{
    float dev, olddev = -1.0, w = 1.0;
    int count = 0;

    do {
        w *= 10.0;
        dev = SPATIALfalseDev2(w, best, probmap, density, ranvals, elements);
        if (debug && myrank == 0)
            fprintf(stderr, "seekMaxWeight: probmap sum = %f\n", 
                    spatialSumF(probmap, elements));
            fprintf(stderr, "seekMaxWeight: w = %f, dev = %f\n", w, dev);

        if (dev == olddev)  {
            if (myrank == 0)
                fprintf(stderr, "seekMaxWeight: weight changed failed\n");
            //exit(EXIT_INSUFFICIENT);
        }
        else
            olddev = dev;

    }  while (count++ < 10 && dev < demand);

    // failed to find a bracketing weight
    if (count >= 8)
        return 0.0;
    else
        return w;
}

// estimateWeight -- accepts a demand value and attempts to
// determine a weight that will match will produce required
// number.
//
// global variables -- ranvals, elements
float estimateWeight(float demand, float best, float delta, 
                     float *probmap, float *density)
{
    int i, count;
    float dev, w, maxw, minw;

    w = maxw = minw = 0.0;

    // PASS 1: bracket the desired weight
    dev = SPATIALfalseDev2(1.0, best, probmap, density, ranvals, elements);
    if (debug && myrank == 0)  {
        fprintf(stderr, "estimateWeight: demand = %f, init dev = %f\n",
                demand, dev);
    }

    if (dev > demand) {
        maxw = 1.0;
        minw = seekMinWeight(demand, best, probmap, density);
        if (minw == 0.0)
            return minw;
    }

    else if (dev < demand) {
        minw = 1.0;
        maxw = seekMaxWeight(demand, best, probmap, density);
        if (maxw == 0.0)
            return maxw;
    }

    if (debug && myrank == 0) {
        fprintf(stderr, "estimateWeight: BRACKET set = %f, %f\n", minw, maxw);
    }

    // PASS 2: bisect the min/max weights to find the desired weight
    w = 1.0;
    count = 0;
    while (count++ < 8) {
        w = minw + (maxw - minw) / 2.0;

        dev = SPATIALfalseDev2(w, best, probmap, density, ranvals, elements);
        if (debug && myrank == 0) {
            fprintf(stderr, "estimateWeight: w = %f, (%f, %f), dev = %f\n",
                    w, minw, maxw, dev);
        }

/*
        if (dev > demand - delta)
            maxw = w;
        else if (dev < demand + delta)
            minw = w;
        else 
            break;
*/
        if (dev > demand)
            maxw = w;
        else if (dev < demand)
            minw = w;
        else 
            break;
    }

    if (debug && myrank == 0) {
        fprintf(stderr, "estimateWeight: w = %f, dev = %f\n", w, dev);
    }
    w = 1.00; //bypass this stupid function - edits by pan at 02/19/2017
    return w;
}

// updateProbRes -- update the current probability WITHOUT the mask
// for developable and nogrowth cells.  
//
// global vars: boundary, probmap_res, nndev, utilities_res, w_probmap_res,
//              w_dynamic_res, w_spontaneous_res, w_utilities_res
//
// Note: this should be called by calcProbRes
void updateProbRes(float *p, int count)
{
    int i;
    // edits by pan - 03/01/2017
    float w, maxp, demand;

    // calculate the demand
    demand = desired_res - current_res;
    if (demand <= 0)  {
        demand = k_min_res;
    }

    if (debug && myrank == 0)  {
       fprintf(stderr, "CalcProbRes: desired=%f, current=%f, demand=%f\n", 
               desired_res, current_res, demand);
    }

    // set the probability map
    for (i=0; i<count; i+=1)  {
      if (boundary[i]) {
        p[i] = powf(probmap_res[i], w_probmap_res)
              + powf(GRAPHinterp(nngraph, nndev[i]), w_neighbors_res)
              //  * powf(1, w_neighbors_res)
               //* powf(nngraph, w_neighbors_res)
               + powf(w_spontaneous_res * drand48() +
                      w_utilities_res * utilities_res[i], w_dynamic_res);
               //         w_utilities_res * 1, w_dynamic_res);
        }
        else
            p[i] = 0.0;
    }
    // add normalization - pan edits 03/01/17
    maxp = spatialMaxF(p, count);
    for (i=0; i<count; i+=1)  {
        p[i] /= (maxp / best_prob_res);
    }

    // estimate that will deliver demand
    w = estimateWeight(demand, best_prob_res, delta_res, p, density_res);
    if (w == 0.0 && myrank == 0)
        fprintf(stderr, "WARNING: failed to establish bracket, w=%f\n", w); 

    for (i=0; i<count; i+=1)  {
        p[i] = (p[i] * w > best_prob_res) ? best_prob_res : p[i] * w;
    }

	
    return;
}

// calcProbRes -- updates the current probabilty 
//
// global vars: probmap_res, nndev, utilities_res, w_probmap_res, 
//              w_dynamic_res, w_spontaneous_res, w_utilities_res,
//              best_prob_res
void calcProbRes(float *p, int count)
{
    int i, avail=0;
    float w, maxp, demand;

    // calculate the demand
    demand = desired_res - current_res;
    if (demand <= 0)  {
        demand = k_min_res;
    }

    if (debug && myrank == 0)  {
       fprintf(stderr, "CalcProbRes: desired=%f, current=%f, demand=%f\n", 
               desired_res, current_res, demand);
    }

    // set the probability map
	fprintf(stderr, "20170401 - count %d\n", count);
    for (i=0; i<count; i+=1)  {
      if (boundary[i] && !nogrowth[i] && developable[i]) {
        avail += 1;
        p[i] = powf(probmap_res[i], w_probmap_res)
               //* powf(nngraph, w_neighbors_res)
               + powf(GRAPHinterp(nngraph, nndev[i]), w_neighbors_res)
               //* powf(1, w_neighbors_res)
               + powf(w_spontaneous_res * drand48() +
                //* powf(w_spontaneous_res * 0 +
                      w_utilities_res * utilities_res[i], w_dynamic_res);
               //         w_utilities_res * 1, w_dynamic_res);
  		//fprintf(stderr, "20170403 - p[i]:  = %f, i = %d, \n",p[i], i);      
		}
        else
            p[i] = 0.0;
    }

	fprintf(stderr, "20170403-1_res - p_res[0]:  = %f, p_res[5264489]:  = %f, p_res[1559170]:  = %f, \n",
                    p[0], p[1],p[1559170]);

    // scale the probability probmap so that max = .25 
    // i.e. highest priority cells have a 25% likelyhood of development
    maxp = spatialMaxF(p, count);
    for (i=0; i<count; i+=1)  {
        p[i] /= (maxp / best_prob_res);
    }

	// 20170407 - would like to add all of these value to globel P | print all of the P first
	//if (check_print == 1) {
		for (i = 0; i < 5264489; i++) {
			// p[i] = p[i] means value not "-NaN"
			if (p[i] != 0 && p[i] && p[i] == p[i]){ 
				//fprintf(stderr, "20170408-calcProbRes - i = %d, p = %f \n", i, p[i]);
				global_res_p_total[i] = (int)(p[i]*1000);
				global_res_p[global_count_res] = (int)(p[i]*1000);
				global_count_res ++;
			}
		}
		fprintf(stderr, "20170407-global_count_res = %d \n", global_count_res);
		global_count_res = 0;
		check_print --;
	//}
 
	fprintf(stderr, "20170403-2_res - p_res[0]:  = %f, p_res[5264489]:  = %f, p_res[1592960]:  = %f, \n",
                    p[0], p[1],p[1592960]);
    // estimate that will deliver demand
    w = estimateWeight(demand, best_prob_res, delta_res, p, density_res);
    if (w == 0.0 && myrank == 0)
        fprintf(stderr, "WARNING: failed to establish bracket, w=%f\n", w); 

    for (i=0; i<count; i+=1)  {
        p[i] = (p[i] * w > best_prob_res) ? best_prob_res : p[i] * w;
    }
	fprintf(stderr, "20170403-3_res - p_res[0]:  = %f, p_res[5264489]:  = %f, p_res[1592960]:  = %f, \n",
                    p[0], p[1],p[1592960]);
	fprintf(stderr, "20170402 - length of p:  = %ld, glob_elements = %d\n",
                    sizeof(p), glob_elements);

    return;
}

// updateProbCom -- update the current probability WITHOUT the mask
// for developable and nogrowth cells.  
//
// global vars: boundary, probmap_com, nndev, utilities_com, w_probmap_com,
//              w_dynamic_com, w_spontaneous_com, w_utilities_com
//
// Note: this should be called by calcProbCom
void updateProbCom(float *p, int count)
{
    int i;
    //edits by pan -03/01/2017
    float w, maxp, demand;

    // calculate the demand
    demand = desired_com - current_com;
    if (demand <= 50)  {
        demand = k_min_com;
    }

    if (debug && myrank == 0)  {
       fprintf(stderr, "CalcProbCom: desired=%f, current=%f, demand=%f\n", 
               desired_com, current_com, demand);
    }

    // set the probability map
    for (i=0; i<count; i+=1)  {
      if (boundary[i]) {
        p[i] = powf(probmap_com[i], w_probmap_com)
               //* powf(nngraph, w_neighbors_com)
                + powf(GRAPHinterp(nngraph, nndev[i]), w_neighbors_com)
               //* powf(1, w_neighbors_com)
               + powf(w_spontaneous_com * drand48() +
               //  * powf(w_spontaneous_com * 0 +
                      w_utilities_com * utilities_com[i], w_dynamic_com);
               //         w_utilities_com * 1, w_dynamic_com);
        }
        else
            p[i] = 0.0;
    // add normalization - pan edits 03/01/17
    maxp = spatialMaxF(p, count);
    for (i=0; i<count; i+=1)  {
        p[i] /= (maxp / best_prob_res);
    }



    // estimate that will deliver demand
    w = estimateWeight(demand, best_prob_res, delta_res, p, density_res);
    if (w == 0.0 && myrank == 0)
        fprintf(stderr, "WARNING: failed to establish bracket, w=%f\n", w); 

    for (i=0; i<count; i+=1)  {
        p[i] = (p[i] * w > best_prob_res) ? best_prob_res : p[i] * w;
    }

    return;
    }
}

// calcProbCom -- updates the current probabilty 
//
// global vars: probmap_com, nndev, utilities_com, w_probmap_com, 
//              w_dynamic_com, w_spontaneous_com, w_utilities_com
//              best_prob_com
void calcProbCom(float *p, int count)
{
    int i;
    float w, maxp, demand;

    // calculate the demand
    demand = desired_com - current_com;
    if (demand <= 50)  {
        demand = k_min_com;
    }

    if (debug && myrank == 0)  {
       fprintf(stderr, "CalcProbCom: desired=%f, current=%f, demand=%f\n", 
               desired_com, current_com, demand);
    }


    // set the probability map
    for (i=0; i<count; i+=1)  {
      if (boundary[i] && !nogrowth[i] && developable[i])
        p[i] = powf(probmap_com[i], w_probmap_com)
               + powf(GRAPHinterp(nngraph, nndev[i]), w_neighbors_com)
               //* powf(1, w_neighbors_com)
               //* powf(nngraph, w_neighbors_com)  
             + powf( w_spontaneous_com * drand48() 
               // powf( w_spontaneous_com * 0
                           + w_utilities_com * utilities_com[i], 
             //                + w_utilities_com * 1,
                         w_dynamic_com);

      else
           p[i] = 0.0;
    }
	fprintf(stderr, "20170403-1_com - p_com[0]:  = %f, p_com[5264489]:  = %f, p_com[1592960]:  = %f, \n",
                    p[0], p[5264489],p[1559170]);
    // scale the probability probmap so that max = .25
    // i.e. highest priority cells have a 25% likelyhood of development
    maxp = spatialMaxF(p, count);
    for (i=0; i<count; i+=1)  {
        p[i] /= maxp * (1.0 / best_prob_com);
    }
	// 20170407 - would like to add all of these value to globel P | print all of the P first
	//if (check_print == 1) {
		for (i = 0; i < 5264489; i++) {
			// p[i] = p[i] means value not "-NaN"
			if (p[i] != 0 && p[i] && p[i] == p[i]){ 
				//fprintf(stderr, "20170408-calcProbCom - i = %d, p = %f \n", i, p[i]);
				global_com_p_total[i] = (int)(p[i]*1000);
				global_com_p[global_count_res] = (int)(p[i]*1000);
				global_count_com ++;
			}
		}
		fprintf(stderr, "20170407-global_count_com = %d \n", global_count_com);
		global_count_com = 0;
		check_print --;
	//}

	fprintf(stderr, "20170403-2_com - p_com[0]:  = %f, p_com[5264489]:  = %f, p_com[1577051]:  = %f, \n",
                    p[0], p[5264489],p[1559170]);
    // estimate that will deliver demand and set the probmap

    w = estimateWeight(demand, best_prob_com, delta_com, p, density_com);
    if (w == 0.0 && myrank == 0)
        fprintf(stderr, "WARNING: failed to establish bracket, w=%f.\n", w); 
    for (i=0; i<count; i+=1)  {
        p[i] = (p[i] * w > best_prob_com) ? best_prob_com : p[i] * w;
		// do not print - fprintf(stderr, "20170331:  p[i]=%f\n", p[i]); 
    }

	fprintf(stderr, "20170403-3_com - p_com[0]:  = %f, p_com[5264489]:  = %f, p_com[1577051]:  = %f, \n",
                    p[0], p[5264489],p[1559170]);
    return;
}

// calcProbOS -- updates the current probabilty 
//
// global vars: probmap_os, nndev, utilities_os, w_probmap_os, 
//              w_dynamic_os, w_spontaneous_os, w_utilities_os


void dumpInitialProbMaps(float *res, float *com, float *os, int count,
                         int time)
{
    char *fname;
    fprintf(stderr, "dumpInitialProb\n");

    if ((fname = SMEgetFileName("INITIAL_PROB_RES_MAP")) != NULL) {
        spatialNormalizeF((float*)outbuf, res, count);
        writeAscGridMap(fname, time, (char*)outbuf, count, MPI_FLOAT);
    }
    if ((fname = SMEgetFileName("INITIAL_PROB_COM_MAP")) != NULL) {
        spatialNormalizeF((float*)outbuf, com, count);
        writeAscGridMap(fname, time, (char*)outbuf, count, MPI_FLOAT);
    }
    if ((fname = SMEgetFileName("INITIAL_PROB_OS_MAP")) != NULL) {
        spatialNormalizeF((float*)outbuf, os, count);
        writeAscGridMap(fname, time, (char*)outbuf, count, MPI_FLOAT);
    }
}


void dumpFinalProbMaps(float *res, float *com, float *os, int count, int time)
{
    char *fname;

    if ((fname = SMEgetFileName("FINAL_PROB_RES_MAP")) != NULL) {
        updateProbRes(res, count);
        spatialNormalizeF((float*)outbuf, res, count);
        writeAscGridMap(fname, time, (char*)outbuf, count, MPI_FLOAT);
    }
    if ((fname = SMEgetFileName("FINAL_PROB_COM_MAP")) != NULL) {
        updateProbCom(com, count);
        spatialNormalizeF((float*)outbuf, com, count);
        writeAscGridMap(fname, time, (char*)outbuf, count, MPI_FLOAT);
    }
    if ((fname = SMEgetFileName("FINAL_PROB_OS_MAP")) != NULL) {
        spatialNormalizeF((float*)outbuf, os, count);
        writeAscGridMap(fname, time, (char*)outbuf, count, MPI_FLOAT);
    }
}


/* Normalize the residential, commercial, and openspace probability
** maps so that the sum is <= 1.0.  This allows the single dice roll
** (range 0-1) determine the change within the cell.
*/

//this is stupid. just throw it away - pan edits 02/20/2017
void normalizeProbMaps(float *res, float *com, float *os, int count)
{
    int i;
    double psum;

    for (i=0; i<count; i+=1)  {
        psum = res[i] + com[i] + os[i];
        if (psum > 0.0)  {
            res[i] = res[i] * res[i] / psum;
            com[i] = com[i] * com[i] / psum;
            os[i] = os[i] * os[i] / psum;
        }
        else
            res[i] = com[i] = os[i] = 0.0;
    }
}


// Develops cells and mark the results in the necessary maps
// and returns updated current growth and count variables
//
// local variables (unique to LU class being developed) :
//   current -- reference to total current development for given lu class
//   count   -- reference to the total cell count for the given lu class
//   p       -- pointer to the probability map
//   density -- pointer to the density map
//   class   -- the LU class as recorded in the change map
//   itr     -- the iteration as recorded in the summary map
// 
// global variables:
//   ranvals -- current array of random values
//   change  -- records new class for cells that have changed class
//   summary -- records iteration of change for celss that have changed class
//   elements - number of active elements arrays
void developCells(float *current, int *count, float *p, 
                  float *density, int class, int itr)
{
    int i;

    for (i=0; i<elements; i+=1)  {
   //     if ((ranvals[i] < p[i]) && (density[i] > MIN_DENSITY))  { #dump stupid density -pan edits 02/20/2017
          if (ranvals[i] < p[i]) {
            change[i] = class;
            lu[i] = class;
            summary[i] = itr;
            *current += density[i];
            *count += 1;
        }
    }
}


void updateLU(unsigned char *lu, unsigned char *change, int count)
{
    int i;

    for (i=0; i<count; i+=1)
        if (change[i]) lu[i] = change[i];
}

/*
float getRandom(float input){
	float result;
	while (result <= input * 1.05 || result >= input * 0.95){
		result = input + drand48()*0.1;

	}
	fprintf(stderr, "20170310 sfk random: %f\n", result);
	return result;
}
*/

float rand_val(){
	srand(time(NULL));
	float a = ((rand()%500 + rand()%500)/(float)10000)-0.05;
	return a*1.75/(float)3;
}

void updateRandom(float *rand, int count, int itr)
{
    char fname[1024], *cptr;
    int i;
    float *newr;

    if (debug && myrank == 0)
        fprintf(stderr, "updateRandom called\n");
        srand(time(NULL));
	    float rdm = rand_val();
		fprintf(stderr, "20170426 res: %f, com: %f", fp_res, fp_com);
	    float rand_fpval = ((fp_res/100000) * (0.6875) + (fp_com/100000) * (-1.45) ) + rdm;
	    if (rand_fpval > 0.202) 
			rand_fpval = 0.202;
        else if (rand_fpval < 0.175) 
			rand_fpval = 0.175;
    // if no maps given just (re-)fill buffer and return 
    //if ((cptr = SMEgetFileName("RANDOM_MAP")) == NULL)  { - force run -edits by Pan 02/17/2017

		//best_prob_res = 0.230, best_prob_com = 0.220 20170425
		best_prob_res = best_prob_res - ((fp_res - 12550)/7362) * 0.001;
		best_prob_com = best_prob_com + ((fp_com - 4000)/4700) * 0.001;
		if (best_prob_res > 0.27) best_prob_res = 0.27;
		else if (best_prob_res < 0.205) best_prob_res = 0.205;
	
		if (best_prob_com > 0.22) best_prob_com = 0.22;
		else if (best_prob_com < 0.205) best_prob_com = 0.205;


        for (i=0; i<count; i+=1){
   //         rand[i] = drand48(); -edits by Pan 02/17/2017
			  //rand[i] = global_res_pval; //20170414
			  //rand[i] = rand_fpval;
				rand[i] = 0.20;
		}
        return;
    //} -force run -edits by Pan 02/17/2017

    // insert itr value if requested 
    sprintf(fname, cptr, itr);
    
    // Warning: new random value grid map isn't free'd
    // causing a memory leak.  But since this method is only
    // used for portability testing we'll live with it.
    //
    // Need grid structure!
    //
    //newr = (float *)initGridMap(fname, count, sizeof (float));
    //for (i=0; i<count; i+=1)
    //    rand[i] = newr[i];

    //return;
}
 

// readProbmap -- check to see if a new probmap is available
// and loads it if necessary. If 'year' is 0 or -1 then it is ignored.
//
// Note: kind of hack! Probably should use access() instead of the open
void readProbmap(float **p, int count, int type, char *name, int year)
{
    FILE *f;
    char *ptr, fname[256], pname[256];

    //if (year > 0)  { * do not update probmap -edits by pan at 02/17/2017
    if (year == 33554432){
        strcpy(pname, name);
        ptr = strrchr(pname, '.');
        *ptr = '\0';
        // sprintf(fname, "%s_%d.%s", pname, year, ptr+1);
        sprintf(fname, "%s.%s", pname, ptr+1);  //Test without year 
    }

    else {
        strcpy(fname, name);
    }

    fprintf(stderr, "#1575 Looking for probmap %s\n", fname);
    if ((f = fopen(fname, "r")) != NULL)  {
        fclose(f);
        freeGridMap((char *)*p, type);

        fprintf(stderr, "#1580 Reading %s\n", fname);
        *p = (float *)initGridMap(fname, count, type);
    }
}

/* calculation res & com incresement 20170308 - jd
*/
float calIncre(float demandEnd, float demandStart, float startTime, float endTime){


	fprintf(stderr, "20170307 --> starttime: %f\n", demandStart );
	float increment = (demandEnd - demandStart)/(endTime - startTime);
	fprintf(stderr, "20170309: probres=%lu, lu=%lu \n", sizeof(resprob), sizeof(lu));
	return increment;
}

/*  20170407-20170405-load file at /home/username/Documents/springfield/trunk/gluc/Data/projection.txt
	for each line --> sep by ","
	1st year start - year end
	2nd pop1 start, pop2 end --> 
	3rd emp1 start, emp2 end -->
*/
void load_projection(){

	char cwd[1024];
	char *whole_dir;
	// get url
	if (getcwd(cwd,sizeof(cwd)) != NULL) {
		char projection_file_dir[] = "/gluc/Data/projection.txt";
		
		whole_dir = malloc(strlen(cwd) + strlen(projection_file_dir) +1);
		strcpy(whole_dir, cwd);
		strcat(whole_dir, projection_file_dir);
		
		fprintf(stderr,"20170407-2-Current dir:%s%s and whole%s \n", cwd,projection_file_dir,whole_dir);		
	} else {
		perror("getcwd() error");
	}
	// open the file
	FILE * pjn;
	char buff[255];
	pjn = fopen(whole_dir,"r");
 
	fgets(buff, 255, (FILE*)pjn);//don't use fgets?
	fprintf(stderr, "20170407-3 filescan: %s\n", buff);
	
	// sep by ","
	char *token;
	char *string;
	char *tofree;
	string = strdup(buff);
	if (string != NULL){
		tofree = string;
		int i = 1;
		while (( token = strsep(&string, ",")) != NULL ) {
			fprintf(stderr, "20170407-4 %s\n",token);
			printf("tooooooooooooken %s\n",token);
			int inputNum = atoi(token);
			// if there are more then two Proj years, there will be a problem. (which only save the 1st and 2nd year)
			if (i == 1) pop1 = inputNum;
			else if (i == 2) pop2 = inputNum;
			else if (i == 3) emp1 = inputNum;
			else if (i == 4) emp2 = inputNum;	
			i++;
		}
		free(tofree);
	} 

	fprintf(stderr, "20170407-2-Proj res_start = %d, res_end = %d, com_start = %d, com_end = %d \n", pop1, pop2, emp1, emp2);
	fclose(pjn);	
	free(whole_dir);
}



void quickSort( int a[], int l, int r)
{
   int j;

   if( l < r ) 
   {
   	// divide and conquer
        j = partition( a, l, r);
       quickSort( a, l, j-1);
       quickSort( a, j+1, r);
   }
	
}



int partition( int a[], int l, int r) {
   int pivot, i, j, t;
   pivot = a[l];
   i = l; j = r+1;
		
   while( 1)
   {
   	do ++i; while( a[i] <= pivot && i <= r );
   	do --j; while( a[j] > pivot );
   	if( i >= j ) break;
   	t = a[i]; a[i] = a[j]; a[j] = t;
   }
   t = a[l]; a[l] = a[j]; a[j] = t;
   return j;
}



/* Run the LUC Model - 
*/
void LUCrun(){
    int i, time, itr = 0;
    int res, com, os;
    int stime, etime, timestep;
    float *rsum = NULL;
    int *rcount = NULL;
    char *cptr;
    unsigned char *mask;
    double score;
    stime = SMEgetInt("START_DATE", 0);
    etime = SMEgetInt("END_DATE", 0);
    timestep = SMEgetInt("TIMESTEP", 1);

    if (debug && myrank == 0)  {
		float increment_res = calIncre(GRAPHinterp(demandres, etime), GRAPHinterp(demandres, stime), (float)stime, (float)etime);
		float increment_com = calIncre(GRAPHinterp(demandcom, etime), GRAPHinterp(demandcom, stime), (float)stime, (float)etime);

		fprintf(stderr, "20170308 --> result_res: %f, result_com= %f \n", increment_res,increment_com);
		fprintf(stderr, "20170315 --> demandres: %p, demandcom: %p \n", (void *) &demandres, (void *) &demandcom);
		fprintf(stderr, "20170317-2 --> A: %f, B: %f \n", GRAPHinterp(demandres, 2011), GRAPHinterp(demandcom, 0));

        fprintf(stderr, "LUCrun: start=%d, end=%d, timestep=%d\n",
                stime, etime,timestep); 
        fprintf(stderr, "starting res = %f, starting com = %f\n",
                GRAPHinterp(demandres, stime), GRAPHinterp(demandcom, stime));
        fprintf(stderr, "ending res = %f, ending com = %f\n",
                GRAPHinterp(demandres, etime), GRAPHinterp(demandcom, etime));
        fprintf(stderr, "total res = %f, total com = %f\n", 
                GRAPHinterp(demandres, etime) - GRAPHinterp(demandres, stime),
                GRAPHinterp(demandcom, etime) - GRAPHinterp(demandcom, stime));

		fp_res = GRAPHinterp(demandres, etime) - GRAPHinterp(demandres, stime);
		fp_com = GRAPHinterp(demandcom, etime) - GRAPHinterp(demandcom, stime);
    }

    // pre-run the diffusion model the specified number of iterations
    if (debug && myrank == 0)
        fprintf(stderr, "Initializing diffusion out %d steps\n", 
                diffusion_init_step);
    for (i=1; i<diffusion_init_step; i+=1)  {
        spatialDiffusion(utilities_res, utilities_tmp, diffusion_rate, 
                        diffusion_res_flags, lu, erow-srow, gCols);
        spatialDiffusion(utilities_com, utilities_tmp, diffusion_rate, 
                        diffusion_com_flags, lu, erow-srow, gCols);
        spatialDiffusion(utilities_os, utilities_tmp, diffusion_rate_os, 
                        diffusion_os_flags, lu, erow-srow, gCols);
    }

    // Ensure we attempt to read probmaps with start time (stime)
    // in their names.
    readProbmap(&probmap_res, elements, sizeof (float),
                //SMEgetFileName("PROBMAP_RES"), stime); - change stime to 0 - edits by pan at 02/17/2017
                  SMEgetFileName("PROBMAP_RES"), stime);
    readProbmap(&probmap_com, elements, sizeof (float),
                //SMEgetFileName("PROBMAP_COM"), stime); - change stime to 0 - edits by pan at 02/17/2017
                  SMEgetFileName("PROBMAP_COM"), stime);
   
/*
	// 20170327 - lu_count_res, lu_count_com
	fprintf(stderr, "20170327-1 - lu_count_res = %d, lu_count_com = %d\n", lu_count_res, lu_count_com);
	float dev_percengate_res = (float)GRAPHinterp(demandres, etime)/(float)pop1;
	float dev_percengate_com = (float)GRAPHinterp(demandcom, etime)/(float)emp1;
    fprintf(stderr, "20170327-2 - percentage_res = %f, percentage_com = %f\n", dev_percengate_res,dev_percengate_com  );
	float final_developable_res = (float)lu_count_res * dev_percengate_res;
	float final_developable_com = (float)lu_count_com * dev_percengate_com;
    fprintf(stderr, "20170327-3 - final_developable_res = %f, developable_com = %f\n", final_developable_res,final_developable_com  );
*/



	// load file at /home/username/Documents/springfield/trunk/gluc/Data/projection.txt
	// for each line --> sep by ","
	// 1st year start - year end
	// 2nd pop1 start, pop2 end --> 
	// 3rd emp1 start, emp2 end -->
	load_projection();


    //   MAINLOOP
    for (time=stime+timestep; time<etime+timestep; time+=timestep)  {
        itr += 1;
		fprintf(stderr, "20170310-4 --> A: %d, B: %d \n", lu_count_res, lu_count_com);
        if (debug && myrank == 0)  {
            fprintf(stderr, "\n\n\nStarting time %d, iteration = %d\n",
                    time, itr);
        }

        // Attempt to read probmaps for the current time period.
        // Warning: if timestep is > 1 then it is possible to miss
        // reading existing probmaps.
        readProbmap(&probmap_res, elements, sizeof (float),
                    //SMEgetFileName("PROBMAP_RES"), time); - change time to stime - edits by pan at 02/17/2017
                      SMEgetFileName("PROBMAP_RES"), time);
        readProbmap(&probmap_com, elements, sizeof (float),
                    //SMEgetFileName("PROBMAP_COM"), time); - change time to stime - edits by pan at 02/17/2017
                      SMEgetFileName("PROBMAP_COM"), time);

        desired_res = GRAPHinterp(demandres, time) - 
                      GRAPHinterp(demandres, stime);
        desired_com = GRAPHinterp(demandcom, time) - 
                      GRAPHinterp(demandcom, stime);

        if (openspace_los > 0)
            desired_os = openspace_los * desired_res;

        if (debug && myrank == 0)
            fprintf(stderr, "desired growth: res = %f, com = %f, os = %f\n", 
            desired_res, desired_com, desired_os);


        nearestNeighbors(nndev, nntmp, RES_FLAG | COM_FLAG, lu, 
                         erow-srow, gCols);
        nearestNeighbors(nnres, nntmp, RES_FLAG, lu, erow-srow, gCols);
        nearestNeighbors(nncom, nntmp, COM_FLAG, lu, erow-srow, gCols);
#ifdef OPENSPACE
        nearestNeighbors(nnos, nntmp, OS_FLAG, lu, erow-srow, gCols);
#endif


		// 20170327 - lu_count_res, lu_count_com
		fprintf(stderr, "20170327-1 - lu_count_res = %d, lu_count_com = %d\n", lu_count_res, lu_count_com);
		float dev_percengate_res = (float)GRAPHinterp(demandres, etime)/(float)pop1;
		float dev_percengate_com = (float)GRAPHinterp(demandcom, etime)/(float)emp1;
		fprintf(stderr, "20170327-2 - percentage_res = %f, percentage_com = %f\n", dev_percengate_res,dev_percengate_com  );
		real_dev_res = (float)lu_count_res * dev_percengate_res;
		real_dev_com = (float)lu_count_com * dev_percengate_com;
		fprintf(stderr, "20170327-3 - final_developable_res = %f, developable_com = %f\n", real_dev_res,real_dev_com  );

        // 20170327 =  temp change
		// desired_res = final_developable_res;
		// desired_com = final_developable_com;

        // updateRandom(ranvals, elements, itr);


        // COMMERCIAL DEVELOPMENT
        spatialDiffusion(utilities_com, utilities_tmp, diffusion_rate, 
                        diffusion_com_flags, lu, erow-srow, gCols);
        if (desired_com - current_com > delta_com)  {
            flagDevelopable(developable, lu, elements, nondevelopable_flags);
			//20170327 - next works            
			calcProbCom(comprob, elements);
			//fprintf(stderr, "20170308 %f \n", (float)sizeof(developable));
            developCells(&current_com, &cell_count_com, comprob, density_com,
                        LU_COM, itr); 
            com = spatialCount(lu, elements, LU_COM);
        }

        else if (debug && myrank == 0) {
            fprintf(stderr, "Skipping COM: demand = %f, delta = %f\n",
                    desired_com - current_com, delta_com);
        }
        

        // RESIDENTIAL DEVELOPMENT
        spatialDiffusion(utilities_res, utilities_tmp, diffusion_rate, 
                        diffusion_res_flags, lu, erow-srow, gCols);
        if (desired_res - current_res > delta_res)  {
            flagDevelopable(developable, lu, elements, nondevelopable_flags);
            calcProbRes(resprob, elements);
            developCells(&current_res, &cell_count_res, resprob, density_res,
                     LU_LRES, itr); 
            res = spatialCount(lu, elements, LU_LRES);
        }

        else if (debug && myrank == 0) {
            fprintf(stderr, "Skipping RES: demand = %f, delta = %f\n",
                    desired_res - current_res, delta_res);
        }

		// 20170327 - from the p_com = comprob & p_res = resprob, sort and get the p, get p[dev]
		fprintf(stderr, "20170329 P_COM:  = %p, P_RES = %p\n",
                    comprob, resprob);
		// 20170331 - dev_com and dev_res        
		
		fprintf(stderr, "20170331 - glob-real_dev_res:  = %f, glob-real_dev_com = %f\n",
                    real_dev_res, real_dev_com);

		fprintf(stderr, "20170401 - developable_test0:  = %f, developable_test= %f\n",
                    comprob[(int)real_dev_res], resprob[(int)real_dev_com]);
		//calcProbRes
		fprintf(stderr, "20170407 - 20170402 - comprob[1559170]:  = %f, resprob[1559170]= %f, glob_elements = %d\n",
                    comprob[1559170], resprob[1559170], glob_elements);

		//20170408-20170403-sort all global_res/com_p
		//global_res_p_total[i]
		
		// == 0 not run, == 1 run once
		if (compute_global_p == 0) {
			//int i, j, swap;
			
			//int a[] = { 7, 12, 1, -2, 0, 15, 4, 11, 9};

			//int i;
			//printf("\n\nUnsorted array is:  ");
			//for(i = 0; i < 9; ++i) printf(" %d ", a[i]);

			quickSort( global_res_p, 0, sizeof(global_res_p)/sizeof(global_res_p[0]));
			quickSort( global_com_p, 0, sizeof(global_com_p)/sizeof(global_com_p[0]));
			//printf("\n\nSorted array is:  ");
			//for(i = 0; i < 9; ++i) printf(" %d ", a[i]);

			/*
			for (i = 0; i < sizeof(global_res_p)/sizeof(global_res_p[0]); i++) {
				for (j = i+1; j < sizeof(global_res_p)/sizeof(global_res_p[0]); j ++) {
					if (global_res_p[i] < global_res_p[j]) {
						swap = global_res_p[i];
						global_res_p[i] = global_res_p[j];
						global_res_p[j] = swap;
					}
				}
			}
			 
			for (i = 0; i < sizeof(global_com_p)/sizeof(global_com_p[0]); i++) {
				for (j = i+1; j < sizeof(global_com_p)/sizeof(global_com_p[0]); j ++) {
					if (global_com_p[i] < global_com_p[j]) {
						swap = global_com_p[i];
						global_com_p[i] = global_com_p[j];
						global_com_p[j] = swap;
					}
				}
			}
			*/

		
			compute_global_p--;
		}

		// when use rev_quicksort
		//real_dev_res = 2000000 - (int)real_dev_res;
		//real_dev_com = 2000000 - (int)real_dev_com;

		//print all global_P[n], P[x] is >0, P[0] > P[1] 
		//global_res_pval = global_res_p[(int)real_dev_res];
		//global_com_pval = global_com_p[(int)real_dev_com];



		fprintf(stderr, "20170407 - global_res_p[j]= %f, global_com_p[k]= %f, elements = %d, j=%d, k=%d    \n",
                    global_res_pval, global_com_pval, elements,(int)real_dev_res,(int)real_dev_com);


		fprintf(stderr, "20170408 - global_res_p[0]= %f,global_res_p[3]= %f,global_res_p[5]= %f, global_res_p[j]:  = %f \n\t\tglobal_com_p[0]= %f,global_com_p[3]= %f,global_com_p[5]= %f,global_com_p[k]= %f,    \n",
                   global_res_p[0],global_res_p[3],global_res_p[5], global_res_pval, global_com_p[0], global_com_p[3], global_com_p[5],global_com_pval);		

		
		updateRandom(ranvals, elements, itr);

		
#ifdef OPENSPACE
        // OPENSPACE DEVELOPMENT
        spatialDiffusion(utilities_os, utilities_tmp, diffusion_rate_os, 
                        diffusion_os_flags, lu, erow-srow, gCols);
        flagDevelopable(developable, lu, elements, nondevelopable_flags);
        calcProbOS(osprob, elements);
        developCells(&current_os, &cell_count_os, osprob, density_os,
                     LU_OS, itr); 
#endif

        shareGrid(change, elements, MPI_UNSIGNED_CHAR);
        updateLU(lu, change, elements);

        // Dump initial probmaps if they are requested
        // Note: technically we should identify these as 'time' rather
        // than 'stime' but confuses users so we'll stick stime.
        // do not dump initial probmap and always use it - edits by pan at 02/17/2017
        //if (itr == 1)
        //    dumpInitialProbMaps(resprob, comprob, osprob, elements, stime);

        if (debug && myrank == 0)  {
            fprintf(stderr, "ITR %d: cell_count_res = %d, current_res = %f\n",
                    itr, cell_count_res, current_res);
            fprintf(stderr, "ITR %d: cell_count_com = %d, current_com = %f\n",
                    itr, cell_count_com, current_com);
        }
    }

    // Dump the final probability maps if requested in config
    //dumpFinalProbMaps(resprob, comprob, osprob, elements, etime);

    /* ending landuse counts */
    res = spatialCount(lu, elements, LU_LRES);
    com = spatialCount(lu, elements, LU_COM);
    os = spatialCount(lu, elements, LU_OS);


    writeAscGridMap(SMEgetFileName("FINAL_DIFFUSION_RES_MAP"), etime,
                 (char *)utilities_res, elements, MPI_FLOAT);
    writeAscGridMap(SMEgetFileName("FINAL_DIFFUSION_COM_MAP"), etime,
                 (char *)utilities_com, elements, MPI_FLOAT);
    writeAscGridMap(SMEgetFileName("FINAL_DIFFUSION_OS_MAP"), etime,
                 (char *)utilities_os, elements, MPI_FLOAT);

    writeGridMap(SMEgetFileName("FINAL_LAND_USE_MAP"), etime, (char*)lu, 
                 elements, MPI_UNSIGNED_CHAR);
    writeGridMap(SMEgetFileName("FINAL_CHANGE_MAP"), etime, (char*)change,
                 elements, MPI_UNSIGNED_CHAR);
    writeGridMap(SMEgetFileName("FINAL_TEMPORAL_MAP"), etime, (char*)summary,
                 elements, MPI_UNSIGNED_CHAR);
    writeGridMap(SMEgetFileName("FINAL_SUMMARY_MAP"), etime, (char*)summary,
                 elements, MPI_UNSIGNED_CHAR);

    writeGridMap(SMEgetFileName("FINAL_LAND_USE_CHANGE_MAP"), etime, 
                 (char*)change, elements, MPI_UNSIGNED_CHAR);

    if (debug)
        fprintf(stderr, "P%d: Model Run Complete\n", myrank);

	//fprintf(stderr, "20170309: %f \n", (float)resprob[418]);
    // WARNING: the following code is running only on the root processor.
    // Do NOT attempt computations that require all processors.
    if (myrank == 0)  {
        itr -= 1;
        printf("Run Report\n");
        printf("Start Time = %d, Ending Time = %d, actual iterations = %d\n",
                stime, etime, itr);
        printf("\n");

        if (SMEgetFileName("PROBMAP_RES"))  {
          printf("Residential Variables\n");
          printf("Static Probability Map = %s\n", 
                 SMEgetFileName("PROBMAP_RES"));
          printf("w_utilities_res=%f\nw_spontaneous_res=%f\n",
                 w_utilities_res, w_spontaneous_res);
          printf("w_neighbors_res=%f\nw_probmap_res=%f\nw_dyanmic_res=%f\n",
                 w_neighbors_res, w_probmap_res, w_dynamic_res);
          printf("\n");
        }

        if (SMEgetFileName("PROBMAP_COM"))  {
          printf("Commerical Variables\n");
          printf("Static Probability Map = %s\n", 
                 SMEgetFileName("PROBMAP_COM"));
          printf("w_utilities_com=%f\nw_spontaneous_com=%f\n",
                 w_utilities_com, w_spontaneous_com);
          printf("w_neighbors_com=%f\nw_probmap_com=%f\nw_dyanmic_com=%f\n",
                 w_neighbors_com, w_probmap_com, w_dynamic_com);
          printf("\n");
        }

#ifdef OPENSPACE
        if (SMEgetFileName("PROBMAP_OS"))  {
          printf("Openspace Variable\n");
          printf("Static Probability Map = %s\n", 
                 SMEgetFileName("PROBMAP_OS"));
          printf("w_utilities_os=%f\nw_spontaneous_os=%f\n",
                 w_utilities_os, w_spontaneous_os);
          printf("w_neighbors_os=%f\nw_probmap_os=%f\nw_dyanmic_os=%f\n",
                 w_neighbors_os, w_probmap_os, w_dynamic_os);
          printf("\n");
        }
#endif

        printf("Initial Maps\n");
        printf("Landuse Map = %s\n", SMEgetFileName("LU_MAP"));
        if ((cptr=SMEgetFileName("NOGROWTH_ZONE_MAP")) != NULL)
          printf("Nogrowth Map = %s\n", cptr);
        if ((cptr=SMEgetFileName("FLOODZONE_MAP")) != NULL)
          printf("Floodzone Map = %s\n", cptr);
        printf("\n");

        printf("Landuse Change\n");
        printf("Actual Change Cells: Res = %d, Com = %d, OS = %d\n", 
                cell_count_res, cell_count_com, cell_count_os);

        printf("Desired Change: Res = %.2f, Com = %.2f, OS = %.2f\n", 
                GRAPHinterp(demandres, etime) - GRAPHinterp(demandres, stime),
                GRAPHinterp(demandcom, etime) - GRAPHinterp(demandcom, stime),
                GRAPHinterp(demandos, etime) - GRAPHinterp(demandos, stime));

        printf("Actual Change: Res = %.2f, Com = %.2f, OS = %.2f\n", 
                current_res, current_com, current_os);

    }
}
