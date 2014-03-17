package final_2d;

/**
 *
 * @authors- Piyali Mukherjee, Aniruddh Bhat & Prof. KR Phaneesh. This source code is property of Prof. K.R.Phaneesh
 * (phaneeshkr@msrit.edu). Please contact him for any references, or copies, or intended modifications. The code is made available
 * free for educational purposes, and it is expressly forbidden to seek any financial consideration in exchange of distributing the
 * code in any form including donations or defraying "beer" expenses. The same applies to its translations, including translations
 * into C, C++, or other computing and human languages.
 *
 * No warranty is implied, and the authors explicitly warn the users that there is no stated or implied suitability for any purpose,
 * and even if there are any liabilities, the user, or the person who is copying this code, hereby acknowledges that the maximum
 * liability by the authors for any damage direct, or consequential, is limited to what the authors received as a consideration
 * which amounts to zero in any currency.
 *
 * This version implements the final optimized version. This version implements logically four separate thread approach, main and
 * three fired from main - respectively, one for computing initial matrix statistics, which literally copies off the entire matrix
 * and the data into a set of variable all starting with prefix long_. The second thread is fired from the main thread at the end of
 * min_ini_mcs_to_wait Monte Carlo steps, and in an infinite loop, sleeps on the flag "new_copy_given" and whenever it receives a
 * new copy, it computes the statistics like grain count, grain sizes, Hamiltonian, etc. on a snapshot of the state_matrix. This
 * offload allows the main thread to become faster. The tracker add considerable load to the computation. The third one is spawned
 * off the main thread fairly early, and just handles the display image refresh and computes.
 *
 * The initial matrix is separately computed in a separate thread because it poses immense computational load - as the logic
 * requires that the program computing the area needs to fire approximately as many threads as there are grains, though not all
 * concurrently - and for extremely large matrices this may sometimes represent 60% of the total compute time taken. By taking it
 * off the main thread, we achieve a better load balancing between threads. This phenomenon is clearly corroborated by rising CPU
 * utilization levels. The subsequent MCS steps actually accelerate, so the whole program finishes significantly faster. The display
 * thread merely creates the display frame, and then refreshes the data in it, and also computes the data like top 50 displays, and
 * the most frequent q value data.
 *
 * The main thread spawns off MAX_MAT_THREADS to create the trials for each MC step. This is done by dividing the whole matrix into
 * equal MAX_MAT_THREADS quadrants, and then processing them concurrently.
 *
 * The area compute thread applies the similar logic to compute the Hamiltonian, by spawning off MAX_HAM_THREADS, and that
 * considerably speeds up the Hamiltonian computation. We use the callable method there, as we need to get the value of each
 * quadrant Hamiltonian, and then add it to get the total Hamiltonian. It then proceeds to fire a thread for each grain, and that
 * thread computes the area by an elementary logic of neighbour-search. It utilizes the same logic to compute the perimeter as well.
 * These data sets are then recorded into a grain structure.
 *
 * Since thr Hamiltonian varies rapidly during early iteratuions, but is of relatively lesser interest during later variations, and
 * the grain sizes behave quite the opposite, the program writes the Hamiltonian and the exchange data after each iteration BEFORE
 * the min_ini_mcs_to_wait and once the area compute algorithm takes over, the frequency of the Hamil update is synchronized with
 * that step. This would help set larger values of min_ini_mcs_to_wait because during early phases the grain distribution is
 * relatively of lesser interest, thus making the program faster.
 *
 * Optimization data is present of the programmer's website - www.piyali.name - and is updated whenever the run is made.
 *
 */
import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseMotionListener;
import java.awt.geom.Point2D;
import java.awt.geom.RoundRectangle2D;
import java.awt.image.BufferedImage;
import java.awt.image.ColorModel;
import java.awt.image.WritableRaster;
import java.io.*;
import java.text.DecimalFormat;
import java.text.NumberFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Random;
import java.util.concurrent.*;
import javax.imageio.ImageIO;
import javax.swing.*;

public class Final_2D {

	/*
	 * The following variables act to set the various parameters of the run. The "final" ones act as parameters, and the other as
	 * flag controllers. Please change them to suit the run requirements.
	 */
	static short state_size = 1000;				//size of the matrix
	static short max_q = 32;						//Set the max_q_value, if more than 255, then please add more colours
	static final int no_of_mcs_steps = 30000;		//Set no of iterations, -x for "infinite" where |x| consec iter with const H (must be a multiple of hamil_gaps)
	static final short min_ini_mcs_to_wait = 1000;	//Initial MCS steps deal with extremely fragmented matrix, so skip these many MCS before we start area compute
	static boolean periodic = false;				//choice is between periodic or free edge for guard col and row
	static boolean modified = false;				//for modified, we flip only from existing neighbours
	static double prop_for_T = 0.2;					//Set value of kT for thermal flips (k:Boltzmann constant 1.380x10^-23 J/K
	/*
	 * This section defines the fields pertaining to the reading of previously run files. The idea is to write and create files
	 * under a code subdirectory, and then write the files and read the files into that subdirectory. The code is a string that is
	 * prepended to all files created.
	 */
	static final boolean restart_file = false;		//if this is true, then the matrix file, and data fields are "read" rather than created
	static String code_str = "GRAINS1000";			//All files are created in this directory and contains this string as prepend.

	/*
	 * The following are global constants
	 */
	static final short BASE = (short) (state_size + 2);		//This value is extensively used to form linear addresses, and array sizes
	static final short ARR_LIM = (short) (state_size + 1);	//This value is used extensively in array control loops, and reduces wasted computations
	static final int IMM = 0;								//This value of q_state defines an impurity - immovable grain
	static final int TRIALS = state_size * state_size;		//Total number of trials in one Monte Carlo Step
	static final short MAX_DISPLAY = 200;					//Controls display depth for right panel, cant be final as its read from restart_file
	static short MAX_LIST = MAX_DISPLAY;					//The system however stores info on these many grains in memory for quick recall
	/*
	 * The following variables are used to control the impurities - the first one computes the basic number of impurities. The
	 * second one controls the shape of the imnpurity. The shapes are implemented as separate methods, so that more of them may be
	 * conveniently added. The variable rand_size increases their sizes randomly upto a factor of 10, keeping the shape intact.
	 * Shapes are : 0 - single cell size, these may take random nxn shape, depending on the random_size flag. 1 - symmetric rhombus
	 * of minimum size 13, and proportionally elongatable depending on random_size flag. 2 - elongated rectangles of size 4x2, size
	 * randomly increasable to any nx(n-2) 3 - rods of thickness 1, minimum length 2, randomly elongatable (logically elongated
	 * rectangle of size nx1) 4 - needles of thickness 3 and minimum length 3, and length elongatable randomly 5 - In this case, we
	 * read the impurity map from an external text file, impurity_map.txt,that contains a series of x,y co-ordinates of impurities
	 * If we are reading from an external file, we ignore the stated values of the impurity count, or shapes etc.
	 */
	static int impurity_count = (int) (0.015 * (state_size * state_size));	//Set the number of impurities
	static short impurity_shape = 4;										//choose among comment above
	static boolean random_size = true;										//Whether the impurities are to be allocated will have random size
	static final short max_rand_size = 10;									//The maximum factor of growth for the random size
	/*
	 * The following sections create the static variables. No changes to these should be made by user for configuration, etc.
	 */
	static short[][] state_matrix = new short[BASE][BASE];			//allots the matrix with guard row and column
	static short[][] long_state_matrix;								//This duplicate is used for initial area compute only
	static short[][] state_matrix_copy = new short[BASE][BASE];		//This placeholder is used to compute areas in the area compute thread
	static boolean[] flag_array = new boolean[max_q];				//Allocate the flag matrix
	static int cons_no_flips = no_of_mcs_steps;						//This var is used when we need to run "infinite" MCS - till Ham becomes constant
	static boolean still_more_mcs = false;
	static int[] flips;
	static int[] th_flips;
	static long flip_counter = 0;						//Stores count of number of exchanges
	static long thermal_flips = 0;						//Stores count of the thermal flips
	static short file_save_cntr;						//Tracks the file number. First will be *0.csv
	static String user_dir = "";						//This string will contain all user directory path for reads and writes
	static int mcs_no = 0;
	static int prev_no_of_mcs = 0;
	static int[] q_area;								//Is used to determine the largest possible grain so, optimizes memory allotmemnts
	static PrintWriter dout_grain_list;					//Used for creating the grain list file - is appended to by concurrent threads
	static int total_grains;							//total count of the grains
	/*
	 * The following are used for controlling the number of threads that may be concurrently run. These need to be optimized by
	 * looking at the size of the matrix as against the time it takes to establish a thread. The optimal values for 1,000x1,000 are
	 * given below as default. The optimal value will be smaller (that is each quadrant should be relatively bigger) for smaller
	 * matrices, as very small quadrants will take too much overhead.
	 */
	static final int MAT_SPLIT_SIZE = 20;				//The size of split of the grain matrix along x-axis(or y-axis)
	static final int MAX_MAT_THREADS = MAT_SPLIT_SIZE * MAT_SPLIT_SIZE;	//Number of quadrants to split the matrix into
	static final int SPLIT_SIZE = 20;					//Similarly, size of split of the grain matrix to compute Hamiltonian
	static final int MAX_HAM_THREADS = SPLIT_SIZE * SPLIT_SIZE;			//Number of Hamiltonian computing threads
	/*
	 * The following set of initalizers control the logging aspect of the exchanges to the matrix. We track the flips using two
	 * araays flips[] and th_f;ips, each of size MAX_MAT_THREAD, and contains the count of the flips for respective threads. Thes
	 * eare then summed up at the end of the MCS. Next, for each exchange, we enter the detail;s into an array called as
	 * tracker_buffer, which is an array whose each plane belongs to one thread, and each plane contains a rectangular array of
	 * short integers, 4xnumber of elements. At end of the run, we first check if the space available in buffer is below last time
	 * additions to the buffer or not. If space is not enough, we trigger a write, and reset the buffer. If the space is enough, we
	 * continue. This ensures that we do not write at every cycle. Since number of exchanges goes down exponentially, this
	 * arrangement will give more efficient use of the system time spent to write the buffer.
	 */
	static final boolean set_tracker = false;	//This flag will cause the each MCS to generate a tracker log record, used by a different prog
	static DataOutputStream tracker_out;		//The Buffer file handler
	static final int BUF_SIZE = 4 * TRIALS / MAX_MAT_THREADS;	//The size of the monstrous buffer.
	static int[] tracker_index = new int[MAX_MAT_THREADS];	//Array of counters of exchanges stored in buffer, one each for each thread
	static short[][][] tracker_buffer;			//The gigantic buffer itself.
	/*
	 * The following group implements the display graphics. That thread requires a "freeze" copy of all variables that are being
	 * displayed so that the display does not keep flickering between refreshes. We have currently provided 256 distinct colours for
	 * each q_val. If the q_value is being increased even more, please add more colour to the program.
	 */
	static final int[] colours = {0XFF000000, 0XFFD7C8DE, 0XFF84B3FC, 0XFFBAE9F5, 0XFF6ADE69, 0XFFEFB8D4, 0XFF4C052C, 0XFFB2E0DE, 0XFFF745B6, 0XFF7BFBE8, 0XFF55330A, 0XFF94C6F5, 0XFF55186F, 0XFFFB90BC, 0XFF2F5833, 0XFFB197EE, 0XFF0A9525, 0XFFE7B09E, 0XFF114474, 0XFF0F1555, 0XFF530179, 0XFF82B7EE, 0XFFA8073E, 0XFF16B65B, 0XFF5F751E, 0XFFB8FB62, 0XFF792065, 0XFFFAB961, 0XFF3E735F, 0XFFFBEB2C, 0XFF2D9E47, 0XFF86FE8D, 0XFFD00042, 0XFFD3D567, 0XFF21539F, 0XFFC446FD, 0XFF5813AC, 0XFFDC3EEC, 0XFF61B600, 0XFF8ACCA5, 0XFF3FD803, 0XFFC69895, 0XFF08A56E, 0XFF96C498, 0XFF429843, 0XFF75FC80, 0XFF418956, 0XFFFCE013, 0XFFC80C51, 0XFF46D0D1, 0XFFA25532, 0XFF6996E5, 0XFF139F7C, 0XFFA94EE8, 0XFF574594, 0XFFDC6B98, 0XFF947A27, 0XFF608CF3, 0XFF2F27E0, 0XFF996FD5, 0XFF613B9C, 0XFFF9786B, 0XFF81298E, 0XFF846FE5, 0XFF8708AB, 0XFFEA846A, 0XFF0E51DC, 0XFF39D6C6, 0XFF6A557D, 0XFF6B80E2, 0XFF4C13E0, 0XFF3DF597, 0XFF33DF2D, 0XFF27E7B9, 0XFF5BAC41, 0XFFA4F033, 0XFF639155, 0XFFDBE702, 0XFF1D8BA4, 0XFFAB38DB, 0XFF8CC003, 0XFF5965FF, 0XFFF20E50, 0XFF20C7D5, 0XFFE4A064, 0XFF3DDBA2, 0XFF997D3E, 0XFF6FC682, 0XFF50A764, 0XFF705CEA, 0XFF97AA1C, 0XFFF1A71D, 0XFF0165FC, 0XFF9ECC4A, 0XFF8BD800, 0XFFE56962, 0XFF7DD80F, 0XFFCC5B84, 0XFF48E539, 0XFF992EE0, 0XFF2A4DF1, 0XFFA0639E, 0XFF5654BF, 0XFF1AB5D2, 0XFF842AC1, 0XFFF64762, 0XFFAB4D78, 0XFF3D65FC, 0XFF6ED43A, 0XFFED4A66, 0XFF35DA6F, 0XFF23C9B0, 0XFF0CEF85, 0XFF3A6FF2, 0XFFEB0294, 0XFFA06692, 0XFF587BB2, 0XFFD0863F, 0XFF8210F3, 0XFF8DCA3C, 0XFFF07C1A, 0XFF97D02A, 0XFF8DAA50, 0XFFAE855E, 0XFFC0A920, 0XFF424EFF, 0XFF6442E3, 0XFF42DA70, 0XFFC55570, 0XFF14AECE, 0XFF046420, 0XFFC98228, 0XFFF20062, 0XFF1E3763, 0XFFD652B4, 0XFF133BC0, 0XFF32384B, 0XFF76AFF6, 0XFF8ACA4B, 0XFF7B9365, 0XFFC1C705, 0XFFD26E25, 0XFF6633B5, 0XFF420890, 0XFF2CFEBE, 0XFFCEFCEA, 0XFFD7A621, 0XFF7D37E5, 0XFF1A57EC, 0XFF178060, 0XFF6A0EBF, 0XFFE3FC21, 0XFFD59159, 0XFFD29426, 0XFFB0CFD9, 0XFF9386FF, 0XFF3E527E, 0XFF7712EA, 0XFFE54F73, 0XFF66FA59, 0XFFAC4038, 0XFFEEDC7A, 0XFFD4876F, 0XFFB12539, 0XFF5882E5, 0XFF4366A2, 0XFF56122D, 0XFF48FB8B, 0XFF54A8ED, 0XFF2AB6E6, 0XFF0E2121, 0XFFA650FA, 0XFFF61601, 0XFFAF7A40, 0XFF8D0532, 0XFF9C2246, 0XFF4357D8, 0XFFA86C91, 0XFF1D508F, 0XFF62B174, 0XFF59B1FA, 0XFF16EC69, 0XFFE257E9, 0XFF2B5B7C, 0XFF9DDB0C, 0XFFBD3E26, 0XFF403FD3, 0XFFB5ADBF, 0XFF34838C, 0XFF69C96A, 0XFFE50458, 0XFF80B3F8, 0XFF0F49DB, 0XFFAA3B2D, 0XFF318A29, 0XFF478242, 0XFF2081C0, 0XFF14D400, 0XFF3AC2B8, 0XFF9E6B1C, 0XFF982FA2, 0XFF9EEA77, 0XFFA62D36, 0XFF14D39C, 0XFFF009F9, 0XFF30AE99, 0XFFE01EAD, 0XFF05FC8E, 0XFFAF2EA9, 0XFF8DEA68, 0XFFA25092, 0XFFD2FC70, 0XFFAF1A1B, 0XFFF25187, 0XFFE84436, 0XFFA4F103, 0XFFC6E579, 0XFFF40F87, 0XFFE6BEAF, 0XFF1454B0, 0XFF40F432, 0XFF81B51A, 0XFFC4E6E7, 0XFF581D5D, 0XFF17A269, 0XFF2F8B3E, 0XFFDD33A4, 0XFFDA21E5, 0XFF7025C2, 0XFF61B879, 0XFF3F3AA5, 0XFF389CFB, 0XFF052457, 0XFF097E82, 0XFF0196C1, 0XFF94B073, 0XFFCF55E2, 0XFF40000F, 0XFF11D438, 0XFFAA87D1, 0XFFA228FA, 0XFF6150C7, 0XFF74709D, 0XFF21F41F, 0XFFBE4F46, 0XFF121358, 0XFF23F2F1, 0XFFCE86C9, 0XFF691EAA, 0XFF0761F1, 0XFF3FD84E, 0XFF676655, 0XFF0E8D2F, 0XFFA74818, 0XFF7E8E65, 0XFFD7ED53, 0XFFB329C1};
	static long run_start_time = 0;							//Stores the cumulative running time for display
	static long time_at_last_save = 0;
	static long ini_hamil;							//Stores initial Hamiltonian value
	static long hamil_at_last_save = 0;				//Stores Hamil at last save
	static long exchgs_at_last_save;
	static long thermal_exchgs_at_last_save;
	static int iter_at_last_save = 0;
	static int total_grains_at_last_save;
	static double avg_area_at_last_save;
	static int mcs_at_last_save;
	static long[][] big_grains_list = new long[7][MAX_LIST];				//This stores the top MAX_LIST grain data.
	static long[][] big_grains_list_at_last_save = new long[7][MAX_LIST];	//Used for managing the data copy for the last save
	static boolean first_file_save_cntr = false;
	static boolean in_long_analysis = false;
	static boolean in_saving_stats = false;
	static boolean free_to_compute = false;				//These two flags control the copying of state_matrix to the other thread.
	static boolean new_copy_given = false;
	static boolean never_drawn = true;
	static Double percent_ini_file_analysed;		//This flag is used to inform the graphics system how much of the initial file has been processed
	// The following set is used for analysing clicked grain
	static short mouse_x;
	static short mouse_y;
	static boolean click_set = false;
	static boolean click_processed = false;		//This flag is used to determine if the clicked grain has been processed for area compute
	static short click_q_val;
	static long click_area;
	static long click_perim;
	static int click_total_imp;
	static int click_imp_in_belly;
	static long when_click_processed;
	/*
	 * The following implements the random number generator. This needs to be serialized for implementing segmented iteration count
	 * approach.
	 */
	static Random rand_gen = new Random();
	static boolean debug = false;					//This flag is used to control the debug outputs.
	static int[] debug_xchg_failures = null;
	static long[] debug_xchg_success = null;
	static int debug_avg_mcs_time = 0;
	/*
	 * The following is used to establish the uniformity of the random number generator. The array is filled every time a selected
	 * cell is processed
	 */
	static int[][] frequency = null;

	public static void main(String[] args) throws IOException {
		run_start_time = System.currentTimeMillis();

		if (restart_file == true) {		//we do not create the file, we read it from the files already there.
			/*
			 * We first locate the subdirectory where we have been invked from, and then locate the file with same code string as we
			 * have been invoked from, and containing the largest <num> to <code str>_Grains_matrix_<num>.
			 */
			user_dir = System.getProperty("user.dir");
			if (user_dir.endsWith(code_str) == false) {
				user_dir = user_dir.concat(System.getProperty("file.separator") + code_str + System.getProperty("file.separator"));
			} else {
				user_dir = user_dir.concat(code_str + System.getProperty("file.separator"));
			}
			System.out.println("Reading the files from subdirectory " + user_dir);

			File complete_path = new File(user_dir);
			String[] files_in_dir = complete_path.list();
			String s = "";
			int curr_fil_no;
			int max_fil_no = -1;

			for (int i = 0; i < files_in_dir.length; i++) {
				if (files_in_dir[i].contains("Grains_matrix_") == true) {

					curr_fil_no = Integer.parseInt(files_in_dir[i].substring(files_in_dir[i].lastIndexOf("matrix_") + 7, files_in_dir[i].lastIndexOf(".")));
					if (curr_fil_no > max_fil_no) {
						max_fil_no = curr_fil_no;
						s = files_in_dir[i];
					}
				}
			}
			System.out.println("The file name with code: " + code_str + " in the directory " + user_dir + " with maximum number is: " + s);
			DataInputStream din_dat = new DataInputStream(new BufferedInputStream(new FileInputStream(user_dir + s)));
			/*
			 * Having found the latest file, we read the snapshot from the file. We also set the first_file_save_cntr to false so
			 * that the system later does not fire a parallel thread to compute inital matrix. That is required ONLY when the matrix
			 * is just freshly generated.
			 */
			file_save_cntr = din_dat.readShort();
			state_size = din_dat.readShort();
			max_q = din_dat.readShort();
			hamil_at_last_save = din_dat.readLong();
			periodic = din_dat.readBoolean();
			modified = din_dat.readBoolean();
			prop_for_T = din_dat.readDouble();
			impurity_count = din_dat.readInt();
			impurity_shape = din_dat.readShort();
			flip_counter = din_dat.readLong();
			thermal_flips = din_dat.readLong();
			prev_no_of_mcs = din_dat.readInt();
			total_grains = din_dat.readInt();
			MAX_LIST = din_dat.readShort();
			ini_hamil = din_dat.readLong();

			for (short i = 0; i < BASE; i++) {
				for (short j = 0; j < BASE; j++) {
					state_matrix[i][j] = din_dat.readShort();
				}
			}

			for (short i = 0; i < 7; i++) {
				for (short j = 0; j < MAX_LIST; j++) {
					big_grains_list[i][j] = din_dat.readLong();
				}
			}
			din_dat.close();
			user_dir = user_dir.concat(code_str);
			System.out.println("Reading matrix of size: " + state_size + " max_q: " + max_q + " periodic: " + periodic + " modified: " + modified + " prop_for_T: " + prop_for_T + " impurity count: " + impurity_count + " impurity shape: " + impurity_shape + " already exchanged: " + flip_counter + " and thermal flips: " + thermal_flips + " with previously run: " + prev_no_of_mcs + " iterations, resulting into " + total_grains);
			q_area = new int[max_q];
			file_save_cntr++;
			first_file_save_cntr = false; 	//Because the file_cntr is not zero, the duplicate state matrix, used for computing intial values, is not used.
		} else {
			/*
			 * So, this stretch of code is activated when we start fresh computations. So, we essentially just establish the
			 * complete path to our subdirectory, and the code string, so that all subseqeunt file operations can use this string
			 */
			user_dir = System.getProperty("user.dir");
			if (user_dir.endsWith(code_str) == false) {
				user_dir = user_dir.concat(System.getProperty("file.separator") + code_str);
				boolean dir_created = new File(user_dir).mkdir();
				if (dir_created) {
					System.out.println("Directory: " + user_dir + " created");
				}
				user_dir = user_dir.concat(System.getProperty("file.separator") + code_str);
			} else {
				user_dir = user_dir.concat(System.getProperty("file.separator") + code_str);
			}

			/*
			 * We generate the matrix
			 */
			for (short i = (periodic ? (short) (1) : (short) (0)); i < (ARR_LIM + (periodic ? (short) (0) : (short) (1))); i++) {
				for (short j = (periodic ? (short) (1) : (short) (0)); j < (ARR_LIM + (periodic ? (short) (0) : (short) (1))); j++) {
					state_matrix[i][j] = (short) (1 + rand_gen.nextInt(max_q));	//min value is 1, max value is max_q, and uniformly distributed
				}
			}
			/*
			 * The impurity shapes have been defined in the header section above.
			 */
			if (impurity_count > 0) {
				make_impurities imp = new make_impurities();

				int cum_imp_area = 0;				//Cumulates the impurity area
				while (cum_imp_area < impurity_count) {
					/*
					 * Uncomment the following code section only if you want randomized shapes among 0-4
					 */
					//impurity_shape = (short)(rand_gen.nextInt(5));

					switch (impurity_shape) {
						case 0: //single cell size, these may take random nxn square shape, depending on the random_size flag.
							cum_imp_area += imp.imp_shape_0();
							break;
						case 1: //symmetric rhombus of minimum size 13, and proportionally elongatable depending on random_size flag.
							cum_imp_area += imp.imp_shape_1();
							break;
						case 2: //rectangles of size 4x2, size randomly increasable to any nx(n-2)
							cum_imp_area += imp.imp_shape_2();
							break;
						case 3: //rods of thickness 1, minimum length 2, randomly elongatable (logically elongated rectangle of size nx1)
							cum_imp_area += imp.imp_shape_3();
							break;
						case 4: // needles of thickness 3 and minimum length 5, and length elongatable randomly
							cum_imp_area += imp.imp_shape_4();
							break;
						case 5:
							String imp_defn_line;
							short lines = 0;
							BufferedReader imp_file_in = new BufferedReader(new InputStreamReader(new FileInputStream("impurity_map.txt")));
							while ((imp_defn_line = imp_file_in.readLine()) != null) {
								String[] tokens = imp_defn_line.split(",");
								short imp_row = Short.parseShort(tokens[0]);
								short imp_col = Short.parseShort(tokens[1]);
								if ((imp_row > state_size) || (imp_row < 0) || (imp_col > state_size) || (imp_col < 0)) {
									System.err.println("Invalid data in line " + (lines + 1) + " Ignoring ...");
									continue;
								}
								lines++;
								state_matrix[imp_row][imp_col] = IMM;
							}
							imp_file_in.close();
							impurity_count = 0;			//this will exit the outside while loop
							cum_imp_area = lines;
							break;
						default:
							break;
					}
				} //End of while impurities have not reached desired level
				impurity_count = cum_imp_area;			//Actual may be slightly higher than what was intended due to random shapes
			} //End of if impurities > 0

			/*
			 * The periodicity requires that the matrix edge rows and columns use the mirrored wraparound edges.
			 */
			if (periodic) {
				for (short i = 0; i < state_size; i++) {
					state_matrix[i][0] = state_matrix[i][state_size];			//This version requires us to swap column 0 with col state_size
					state_matrix[i][state_size + 1] = state_matrix[i][1];			//and last column [state_size+1] with column 1
					state_matrix[0][i] = state_matrix[state_size][i];			//Then replace row zero with row state size (last data row)
					state_matrix[state_size + 1][i] = state_matrix[1][i];			//and the last row with row 1
				}
			} //End of periodic

			/*
			 * We compute the initial Hamiltonina of the matrix, and then save the data in a file.
			 */
			ini_hamil = compute_hamil_val(state_matrix);
			try {
				PrintWriter hamil_out = new PrintWriter(new FileWriter(user_dir + "_Hamil.csv", false));
				hamil_out.println("MCS step no, Hamiltonian, No of Exchanges, No of Thermal Flips, No of Grains, Average area");
				hamil_out.println("0," + ini_hamil + ",0,0,,, (The two blank fields may be read from the " + user_dir + "_Grain_data_0.txt file.)");
				hamil_out.close();
			} catch (IOException i) {
			}
			/*
			 * We use the q_area matrix for allocating spaces, and that frequency distribution is computed elsewhere. Here we just
			 * allocate memory.
			 */
			q_area = new int[max_q];
			file_save_cntr = 1;			//Initialize the file counter
			/*
			 * Now we call the area & grain count compute part for the first instance of use of the state_matrix, because that takes
			 * very long processing times. This code mimics the standard code used here for computing the area,but is completely
			 * independent, implying, it does NOT use any variable from the rest of the program, thus making this coode re-entrant,
			 * and capable of independent run. It is expected that this code does not run when the matrix sizes are larger than
			 * 2000, as this slows the processing throughput significantly The first step is to copy the matrix snapshot into
			 * long_state_matrix.
			 */
			if (state_size < 2000) {
				long_state_matrix = new short[BASE][BASE];
				for (short i = 0; i < BASE; i++) {
					for (short j = 0; j < BASE; j++) {
						long_state_matrix[i][j] = state_matrix[i][j];
					}
				}
				//We spawn off the initial matrix computations. The files with 0 extensions will be generated directly there.
				Runnable long_area_count_run = new long_area_analysis();
				Thread long_area_thread = new Thread(long_area_count_run);
				long_area_thread.setPriority(long_area_thread.MIN_PRIORITY);
				long_area_thread.start();
			} else {
				//For larger than size 2000 matrices, we just write the file out, and then use another external program to analyze it. That significantly
				//enhances the compute throughput, as the external progarm is in itself a highly parallel code. For smaller matrices, it does not matter.
				System.out.print("Since the state size is large, writing initial matrix to a file for external processing ...");
				try {
					DataOutputStream dout_dat = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(user_dir + "_Grains_matrix_0.dat")));

					dout_dat.writeShort((short) (0));	//file counter
					dout_dat.writeShort(state_size);
					dout_dat.writeShort(max_q);
					dout_dat.writeBoolean(periodic);
					dout_dat.writeBoolean(modified);
					dout_dat.writeDouble(prop_for_T);
					dout_dat.writeInt(impurity_count);
					dout_dat.writeShort(impurity_shape);
					dout_dat.writeLong(0L);				//flip_counter
					dout_dat.writeLong(0L);				//thermal_flips
					dout_dat.writeInt(0);
					dout_dat.writeInt(0);				//Be careful, this field will have to be recomputed in the external program
					dout_dat.writeShort(MAX_DISPLAY);
					dout_dat.writeLong(ini_hamil);
					for (short i = 0; i < BASE; i++) {
						for (short j = 0; j < BASE; j++) {
							dout_dat.writeShort(state_matrix[i][j]);
						}
					}
					for (short i = 0; i < 7; i++) {
						for (short j = 0; j < BASE; j++) {
							dout_dat.writeLong(0L);				//largest grain list, here written as dummy to be 0 to maintain structure consistency
						}
					}
					dout_dat.close();
					PrintWriter dout_txt = new PrintWriter(user_dir + "_Grains_data_0.txt");
					dout_txt.println("File Reference Number: 0");
					dout_txt.println("state_size: " + state_size);
					dout_txt.println("max_q: " + max_q);
					dout_txt.println("Flag for periodic nature:" + periodic);
					dout_txt.println("Flag for modified replacement: " + modified);
					dout_txt.println("Value for thermal propensity: " + prop_for_T);
					dout_txt.println("Total Impurity Count: " + impurity_count);
					dout_txt.println("Shape of impurities: " + impurity_shape);
					dout_txt.println("Total number of exchanges : 0");
					dout_txt.println("Total number of thermal flips: 0");
					dout_txt.println("Total number of cumulative MCS steps: 0");
					dout_txt.println("Total number of grains: <not computed>");
					dout_txt.println("Average grain size : 0.0");
					dout_txt.println("Initial Hamiltonian of this series of runs: " + ini_hamil);
					long now_time = System.currentTimeMillis();
					dout_txt.println("This file has been saved after " + (now_time - run_start_time) / 1000 + " secs from start.");
					dout_txt.close();

				} catch (IOException i) {
				}

				BufferedImage image = new BufferedImage(state_size, state_size, BufferedImage.TYPE_INT_ARGB);
				WritableRaster raster = image.getRaster();
				ColorModel model = image.getColorModel();

				for (int i = 1; i < ARR_LIM; i++) {
					for (int j = 1; j < ARR_LIM; j++) {
						short q_val = state_matrix[i][j];
						Color shade = new Color(colours[q_val]);
						Object exact_shade = model.getDataElements(shade.getRGB(), null);	//convert the colour into Object form
						raster.setDataElements(i - 1, j - 1, exact_shade);						//set the pixel into the exact shade
					}
				}
				try {
					File png_output = new File(user_dir + "_Grains_image_0.png");
					ImageIO.write(image, "png", png_output);
				} catch (IOException i) {
				}
				System.out.println("Done");
			}
			// The following code kicks in only when a frequency histogram of the MC attempts is required, else keep commented.
			frequency = new int[state_size][state_size];
			for (int i = 0; i < state_size; i++) {
				for (int j = 0; j < state_size; j++) {
					frequency[i][j] = 0;					//Initialize freqeuncy array
				}
			}
		} //end of else of if (restart_file) == true


		/*
		 * The following creates the display image frame, which is refreshed automatically after every 1 second in a separate
		 * thread.
		 */
		Runnable displ = new display_image();
		Thread display_thread = new Thread(displ);
		display_thread.setPriority(display_thread.MIN_PRIORITY);
		display_thread.start();

		/*
		 * Now we proceed to execute the MCS iterations by threading them into concurrent trials on submatrices. This code has the
		 * mechanism of co-ordinating with the thread that conputes area (fired from within the loop after min_ini_mcs_to_wait MCS
		 * steps. Once a MCS is over, it checks if the area compute thread is free - by checking free_to_compute flag. If free, then
		 * it copies the state_matrix to state_matrix_copy, and then sets the new_copy_given flag, which indicates to the area
		 * compute thread a new copy of data is avaliable to proceed. That thread sets the free_to_compute to false and clears it
		 * only when its done with one analysis and is ready for next. Consequently, we have irregular gaps between the MCS when the
		 * area is computed, but in reality, we have two independent threads at work, one busy taking snapshots, and then computing
		 * the area at that snapshot, and the other busy executing MCS. Within each MCS, we just first fire MAX_MAT_THREADS and then
		 * once all threads are home, we sum up the exchanges. Then we check how much of the tracker buffer has been filled up, and
		 * then if required flush the tracker buffer to the file. Then, we just check whether the time to complete the current cycle
		 * has come or not, and if so, then we terminate the main thread. Once we are ready to exit, we just ensure that the tracker
		 * buffer is flushed out completely, and closed. The area compute thread is asked to compute for one last time, and then the
		 * program exits.
		 */

		/*
		 * We start by raising our own priority to the HIGHEST permissible.
		 */
		Thread current_thread = Thread.currentThread();
		current_thread.setPriority(current_thread.MAX_PRIORITY);
		flips = new int[MAX_MAT_THREADS];				//The flip counters are tracked MAX_MAT_THREADS threadwise, and later added up.
		th_flips = new int[MAX_MAT_THREADS];

		//All the following are used only for the debug and optimization scenarios
		short[] debug_mcs_times = null;					//We store run time for the ten MCS and display once during debugs
		long[] debug_tracker_times = null;				//Same thing for tracker file saving operations.
		long st_time = 0;
		long last_displ_time = 0;
		short debug_cntr = 0;							//Counts how many tracker flushes have been executed.

		boolean compute_area_thread_started = false;	//This flag is used to fire the compute area thread at end of mcs cycle for the first time

		if (debug) {
			st_time = System.currentTimeMillis();		//Used for displaying total run times etc. for debugs
			debug_mcs_times = new short[10];
			debug_tracker_times = new long[10];
			debug_xchg_failures = new int[MAX_MAT_THREADS];
			debug_xchg_success = new long[MAX_MAT_THREADS];
		}

		if (set_tracker) {
			tracker_buffer = new short[MAX_MAT_THREADS][4][BUF_SIZE];	//The gigantic buffer itself, allocated only if tracking is on.
		}
		//Now begins the main loop, which we continue till there are MCS steps to perform...

		do { //while there are still more MCS steps to perform
			if (debug) {
				last_displ_time = System.currentTimeMillis();
				for (short i = 0; i < MAX_MAT_THREADS; i++) {
					debug_xchg_failures[i] = 0;
					debug_xchg_success[i] = 0L;
				}
			}

			still_more_mcs = false;
			ExecutorService trials_exec = Executors.newFixedThreadPool(MAX_MAT_THREADS);		//We split the trials into MAX_MAT_THREADS quadrants
			for (int i = 0; i < MAX_MAT_THREADS; i++) {
				flips[i] = 0;																	//Initalize counters
				th_flips[i] = 0;
				Runnable the_runs = new Split_matrix(i);
				trials_exec.execute(the_runs);
			}
			trials_exec.shutdown();								// Executor will accept no new threads and finish all existing threads in the queue
			while (!trials_exec.isTerminated()) {				// Wait until all threads are finished - that will ensure that MCS run is complete
			}

			if (debug && (debug_avg_mcs_time > 25000)) {
				System.out.println("Debug: xchg failures by each thread : avg_mcs: " + debug_avg_mcs_time);
				for (int i = 0; i < MAX_MAT_THREADS; i++) {
					System.out.print("   " + debug_xchg_failures[i]);
				}
				System.out.println();

				System.out.println("Debug: xchg successes by each thread : avg_mcs: " + debug_avg_mcs_time);
				for (int i = 0; i < MAX_MAT_THREADS; i++) {
					System.out.print("   " + debug_xchg_success[i]);
				}
				System.out.println();

				System.out.println("Debug: flip counter by each thread : avg_mcs: " + debug_avg_mcs_time);
				for (int i = 0; i < MAX_MAT_THREADS; i++) {
					System.out.print("   " + (flips[i] + th_flips[i]));
				}
				System.out.println();
			}

			for (int i = 0; i < MAX_MAT_THREADS; i++) {	//These two are global variables, so are NOT initalized, merely accumulated into
				flip_counter += flips[i];
				thermal_flips += th_flips[i];
			}

			/*
			 * The following block is only for debugging purposes
			 */
			if (debug && mcs_no > 1) {
				debug_mcs_times[(mcs_no % 10)] = (short) (System.currentTimeMillis() - last_displ_time);
				if (mcs_no % 10 == 0) {
					debug_avg_mcs_time = debug_mcs_times[0];
					System.out.print("Debug: last ten mcs times: ");
					for (short i = 1; i < 10; i++) {
						debug_avg_mcs_time += debug_mcs_times[i];
						System.out.print("  " + debug_mcs_times[i]);
					}
					System.out.println("  " + debug_mcs_times[0] + " avg: " + (int) (debug_avg_mcs_time / 10));
				}
				last_displ_time = System.currentTimeMillis();
			}
			/*
			 * Update the tracker file
			 */
			if (set_tracker) {
				tracker_out = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(user_dir + "_tracker_file.dat", (!((restart_file == false) && (mcs_no == 0))))));

				boolean time_to_flush = false;					//We check if the time to write down the buffer has come or not
				int k = 0;
				do {
					if (tracker_index[k] >= 0.9 * BUF_SIZE) {
						if (debug) {
							System.out.println("Debug! : " + tracker_index[k] + "  records in tracker index buffer for index " + k + " at mcs_no : " + mcs_no);
						}
						time_to_flush = true;
					}
					k++;
				} while ((time_to_flush == false) && (k < MAX_MAT_THREADS));

				if (time_to_flush) { //Time to write the file
					try {
						for (k = 0; k < MAX_MAT_THREADS; k++) {
							for (int i = 0; i < tracker_index[k]; i++) {
								tracker_out.writeInt(mcs_no);
								tracker_out.writeShort(tracker_buffer[k][0][i]);
								tracker_out.writeShort(tracker_buffer[k][1][i]);
								tracker_out.writeShort(tracker_buffer[k][2][i]);
								tracker_out.writeShort(tracker_buffer[k][3][i]);
							}
							tracker_index[k] = 0;
						}
						/*
						 * This is a time consuming process but will ensure that the tracker is saved after every flush. So the
						 * tracker file is saved even of the whole program is aborted in middle.
						 */

						tracker_out.close();
						tracker_out = new DataOutputStream(new FileOutputStream(user_dir + "_tracker_file.dat", true));
					} catch (IOException e) {
					}

					//Following kicks in only during debugging
					if (debug) {
						debug_tracker_times[(debug_cntr % 10)] = (System.currentTimeMillis() - last_displ_time);
						debug_cntr++;
						if (debug_cntr % 10 == 0) {
							System.out.print("Debug: tracker time at tracker save cntr : " + debug_cntr + " values: ");
							for (short i = 1; i < 10; i++) {
								System.out.print("  " + debug_tracker_times[i]);
								debug_tracker_times[i] = 0;
							}
							System.out.println("  " + debug_tracker_times[0]);
							debug_tracker_times[0] = 0;
						}
					}
				}
			}

			/*
			 * Next we come to analyzing if we must exit the mcs do .. while loop, or we still have to continue to run MCS. So, it
			 * analyses if we have been asked to run infinitely, or have finite number of steps to execute.
			 */
			if (no_of_mcs_steps > 0) {								//do these iterations finitely
				if (mcs_no == no_of_mcs_steps) {
					still_more_mcs = false;						//Time to end the iterations
				} else {
					still_more_mcs = true;			//May appear redundant, but if H does NOT decrease for some iteration, and we still need to complete more iterations
				}
			} else {		//do these infinitely, till no flips in consecutive no_of_iters iterations :-)
				if (still_more_mcs == false) {
					if (++cons_no_flips == 0) {
						still_more_mcs = false;				//Time for true exit
					} else {
						still_more_mcs = true;			//Else, we weary ones have more work to do ...
					}
				} else {
					cons_no_flips = no_of_mcs_steps;				//We reset back the counter, as still_more_mcs == true will imply we cannot start our countdown of consecutive Hamiltonians as constant reason for exit
				}
			}
			/*
			 * This last block is executed only once,after min_ini_mcs_to_wait number of MCS cycles have completed, and triggers off
			 * the thread that computes the area.
			 */

			if ((compute_area_thread_started == false) && (mcs_no > min_ini_mcs_to_wait)) {		//Will get executed only once
				compute_area_thread_started = true;
				iter_at_last_save = mcs_no;
				exchgs_at_last_save = flip_counter;
				thermal_exchgs_at_last_save = thermal_flips;
				free_to_compute = true;
				Runnable comp_area = new compute_area();
				Thread compute_thread = new Thread(comp_area);
				compute_thread.setPriority(compute_thread.MAX_PRIORITY);
				compute_thread.start();

			}
			/*
			 * This block merely checks the flags, and if the area compute process is free to take next data, the snapshot is
			 * copied.
			 */

			if ((compute_area_thread_started) && (free_to_compute)) {
				for (short i = 0; i < BASE; i++) {
					for (short j = 0; j < BASE; j++) {
						state_matrix_copy[i][j] = state_matrix[i][j];
					}
				}
				iter_at_last_save = mcs_no;
				exchgs_at_last_save = flip_counter;
				thermal_exchgs_at_last_save = thermal_flips;
				new_copy_given = true;			//This signals the waiting area compute thread to start computing on the snapshot
			}
			/*
			 * This block actually writes the Hamiltonian to the Hamil.csv file and is active only during initial stages. Once the
			 * thread that measures area has been spawned, this block is not executed, as Hamiltonians are now computed and stored
			 * as a part of the area compute algorithm. This also writes two zeroes at the columns of grains numbers and grain
			 * sizes, as these are also not computed till the area compute algorithm is spawned off.
			 */
			if (!compute_area_thread_started) {
				hamil_at_last_save = compute_hamil_val(state_matrix);
				try {
					PrintWriter dout_hamil = new PrintWriter(new BufferedWriter(new FileWriter(user_dir + "_Hamil.csv", true)));
					int temp = prev_no_of_mcs + mcs_no;
					dout_hamil.println(temp + "," + hamil_at_last_save + "," + flip_counter + "," + thermal_flips + ",0,0");
					dout_hamil.close();		//This ensures that even if the run is terminated in before closure, Hamiltonian is saved
				} catch (IOException e) {
				}
			}
			mcs_no++;
		} while (still_more_mcs); //End of MCS steps

		/*
		 * Now we gracefully terminate the program. To do so, we first execute one more compute iteration, that would give the
		 * "final picture" and then we close and settle the tracker down. So, first, if at the moment of termination, a particular
		 * instance of area compute is running, we wait for that instance to finish. Then we fire one more compute thread.
		 */
		new_copy_given = false;			//This will prevent the area compute loop from starting a new compute cycle
		if (set_tracker) {
			try {
				for (int k = 0; k < MAX_MAT_THREADS; k++) {
					for (int i = 0; i < tracker_index[k]; i++) {
						tracker_out.writeInt(mcs_no);
						tracker_out.writeShort(tracker_buffer[k][0][i]);
						tracker_out.writeShort(tracker_buffer[k][1][i]);
						tracker_out.writeShort(tracker_buffer[k][2][i]);
						tracker_out.writeShort(tracker_buffer[k][3][i]);
					}

				}
				tracker_out.close();
			} catch (IOException e) {
			}
		}
		while (!free_to_compute) {	//The area compute loop is still at work on some last cycle. so we wait till its over
			try {
				Thread.sleep(1);
			} catch (InterruptedException i) {
			}
		}
		for (short i = 0; i < BASE; i++) {
			for (short j = 0; j < BASE; j++) {
				state_matrix_copy[i][j] = state_matrix[i][j];
			}
		}
		exchgs_at_last_save = flip_counter;
		thermal_exchgs_at_last_save = thermal_flips;
		iter_at_last_save = mcs_no;
		new_copy_given = true;
		try {
			Thread.sleep(10);
		} catch (InterruptedException e) {
		}	//Give a moment for the other thread to catch up and start analyzing the last array condition

		while (!free_to_compute) {
			try {
				Thread.sleep(1);
			} catch (InterruptedException i) {
			}
		}
		new_copy_given = false;			//Will ensure that area compute loop does not go on infinitely creating new files
		/*
		 * For matrices whose computes are being done in program and in relatively short runs, it is possible that the main MCS
		 * cycles get over while the initial analysis is still at work. So, we wait for the initial analysis to get over before we
		 * quit
		 */

		while (in_long_analysis) {
			try {
				Thread.sleep(1000);
			} catch (InterruptedException e) {
			}
		}
		//Finally if the frequency is being measured, then execute, else keep the code below commented
		try {
			PrintWriter dout_freq = new PrintWriter(new BufferedWriter(new FileWriter(user_dir + "_freq.csv", true)));
			for (int i = 0; i < state_size; i++) {
				for (int j = 0; j < state_size; j++) {
					if (frequency[i][j] == 0) {
						continue;
					}
					dout_freq.println(frequency[i][j]);
				}
			}
			dout_freq.close();
		} catch (IOException e) {
		}
		System.exit(0);

	}//End of main

	public static class dir_vectors {

		private short start_val_i = 0;
		private short end_val_i = 0;
		private short start_val_j = 0;
		private short end_val_j = 0;
		private boolean is_on_edge = false;

		public dir_vectors() {
			return;
		}

		public boolean set_val(short row, short col) {
			if (row == 1) {
				is_on_edge = true;
				if (col == 1) {
					start_val_i = 0;
					end_val_i = 1;
					start_val_j = 0;
					end_val_j = 1;
				} else {
					if (col == state_size) {
						start_val_i = 0;
						end_val_i = 1;
						start_val_j = -1;
						end_val_j = 0;
					} else {
						start_val_i = 0;
						end_val_i = 1;
						start_val_j = -1;
						end_val_j = 1;
					}
				}
			} else {
				if (row == state_size) {
					is_on_edge = true;
					if (col == 1) {
						start_val_i = -1;
						end_val_i = 0;
						start_val_j = 0;
						end_val_j = 1;
					} else {
						if (col == state_size) {
							start_val_i = -1;
							end_val_i = 0;
							start_val_j = -1;
							end_val_j = 0;
						} else {
							start_val_i = -1;
							end_val_i = 0;
							start_val_j = -1;
							end_val_j = 1;
						}
					}
				} else {
					if (col == 1) {
						is_on_edge = true;
						start_val_i = -1;
						end_val_i = 1;
						start_val_j = 0;
						end_val_j = 1;
					} else {
						if (col == state_size) {
							is_on_edge = true;
							start_val_i = -1;
							end_val_i = 1;
							start_val_j = -1;
							end_val_j = 0;
						} else {
							start_val_i = -1;
							end_val_i = 1;
							start_val_j = -1;
							end_val_j = 1;
						}
					}
				}
			}
			//System.out.println("Debug : for r: "+row+" c: "+col+" st_i: "+start_val_i+" end_i: "+end_val_i+" st_j: "+start_val_j+" end_j: "+end_val_j);
			return (is_on_edge);
		} //End of the method

		public short get_st_val_i() {
			return (start_val_i);
		}

		public short get_st_val_j() {
			return (start_val_j);
		}

		public short get_end_val_i() {
			return (end_val_i);
		}

		public short get_end_val_j() {
			return (end_val_j);
		}
	}

	public static class compute_hamil implements Callable<Long> {

		private short thr_id;
		private long ham;
		private short lt_lim;
		private short rt_lim;
		private short tp_lim;
		private short bt_lim;
		private short STATE_SIZE_PART = (short) (state_size / SPLIT_SIZE);
		private short[][] local_iesm = new short[3][3];
		private short[][] which_matrix;

		public compute_hamil(short thread_no, short[][] which_mat) {
			thr_id = thread_no;
			ham = 0;
			lt_lim = (short) (1 + (thr_id % SPLIT_SIZE) * STATE_SIZE_PART);
			rt_lim = (short) (lt_lim + STATE_SIZE_PART);
			tp_lim = (short) (1 + (thr_id / SPLIT_SIZE) * STATE_SIZE_PART);
			bt_lim = (short) (tp_lim + STATE_SIZE_PART);
			which_matrix = which_mat;
			return;
		}

		@Override
		public Long call() {

			for (short i = lt_lim; i < rt_lim; i++) {
				for (short j = tp_lim; j < bt_lim; j++) {
					if (which_matrix[i][j] == IMM) {
						continue;
					}
					//First we extract an IESM matrix at each location
					for (short x = 0; x <= 2; x++) {
						for (short y = 0; y <= 2; y++) {
							local_iesm[x][y] = which_matrix[i + x - 1][j + y - 1];
						}
					}
					//Then we add to the total
					ham += kron(local_iesm);
				}
			}
			return (ham);
		}

		short kron(short[][] iesm_type) {
			/*
			 * Computes the kronecker delta of the iesm matrix, but returns the hamiltonian (8-sum(kronecker delta));
			 */
			short kron_val = 0;
			for (short x = 0; x <= 2; x++) {
				for (short y = 0; y <= 2; y++) {
					if (iesm_type[x][y] == iesm_type[1][1]) {
						kron_val++;
					}
				}
			}
			kron_val--; //We test all nine times in the loop above, but we should not do a self compare, so we decrease
			return ((short) (8 - kron_val));
		}
	}

	static long compute_hamil_val(short[][] which_matrix) {
		/*
		 * This version splits up the hamiltonian computations into MAX_HAM_THREADS parallel threads, as for large matrices, it
		 * would be faster.
		 */
		ExecutorService hamil_pool = Executors.newFixedThreadPool(MAX_HAM_THREADS);
		java.util.List<Future<Long>> hamil_vals = new ArrayList<Future<Long>>(MAX_HAM_THREADS);
		for (short i = 0; i < MAX_HAM_THREADS; i++) {
			Callable<Long> part_hamil = new compute_hamil(i, which_matrix);
			Future<Long> result = hamil_pool.submit(part_hamil);
			hamil_vals.add(result);
		}
		hamil_pool.shutdown();
		while (!hamil_pool.isTerminated()) {
		}

		long this_hamil = 0;
		for (Future<Long> f : hamil_vals) {
			try {
				this_hamil += f.get();
			} catch (ExecutionException x) {
			} catch (InterruptedException y) {
			}
		}
		return (this_hamil);
	}//End of Hamiltonian calculator

	public static class compute_area implements Runnable {

		NumberFormat fmt_double = new DecimalFormat("###,###,###,##0.000");

		public compute_area() {
			return;
		}

		@Override
		public void run() {
			short flag_array_missed_counter = 0;

			/*
			 * Now we are ready to start the infinite loop of area computation. Each session first waits for the new_copy_given flag
			 * to become true, which would imply that the MCS thread has provided a fresh copy of the state_matrix into
			 * state_matrix_copy It sets a free_to_compute flag as false, thus indicating to the MCS thread that it should not do
			 * any copying, as the previous copy has not yet been completely computed. Therefore, these two flags act as a
			 * semaphore, and ensure that these two processes do not trample upon each other.
			 */
			do {
				while (new_copy_given == false) {
					try {
						Thread.sleep(1);
					} catch (InterruptedException i) {
					}
				}
				new_copy_given = false;
				free_to_compute = false;			//So, now the MCS will NOT provide a fresh copy.
				/*
				 * We first reset the whole big_grains_list array
				 */

				for (short i = 0; i < 7; i++) {
					for (short j = 0; j < MAX_LIST; j++) {
						big_grains_list[i][j] = 0L;
					}
				}

				try {
					/*
					 * Since grains are generated by parallel thread, we keep the output handle open here, and let each thread
					 * append the grain statistics that it has computed. Then at the end of this area compute run, we close the
					 * file.
					 */
					dout_grain_list = new PrintWriter(new BufferedWriter(new FileWriter(user_dir + "_Grains_listing_" + file_save_cntr + ".txt", false)));
					dout_grain_list.println("Seq_no, q value, row, col, area, perimeter, imp within grain, imp on boundary");
				} catch (FileNotFoundException f) {
					System.err.println("File not found in creating new grain list file ... Perhaps out of resources");
				} catch (IOException f) {
				}

				boolean another_pass_to_do;
				short q_val;

				int pass_counter = 0;
				int no_of_threads_in_this_pass;
				total_grains = 0;
				/*
				 * The following is a memory optimization trick. We need a definitive upper limit on number of elements in the
				 * grains list but we obviously do not want to allot a memory element of size state_matrix*state_matrix -
				 * theoretical upper limit. So, we compute the frequency distribution of each q_val, and allot only that much
				 * nmemory as the frequency of that q_val is. The q_areas data is used inside the area computing method, but is
				 * generated here.
				 */

				for (short i = 0; i < max_q; i++) {
					q_area[i] = 0;
					flag_array[i] = false;							//Take the opportunity to initialize flag array as well
				}
				for (short i = 1; i < ARR_LIM; i++) {				//Build the frequency chart of the q_values distribution of array copy
					for (short j = 1; j < ARR_LIM; j++) {
						q_val = state_matrix_copy[i][j];
						if (q_val == IMM) {
							continue;
						}
						q_area[q_val - 1]++;
					}
				}

				/*
				 * This part of the algorithm executes a concurrent implementation of scanning the entire array, firing a thread
				 * each time a new grain is found, and importantly, ensuring that for each q_val, at any time, only one thread is
				 * running. This therefore, requires multiple passes through the array.
				 */
				/*
				 * The do while loop is actually a pass counter, so it is executed till areas of all the grains have been measured.
				 * The loop creates baby threads of max_q count, each baby thread measuring area of a grain, and is fired only when
				 * there is no existing thread measuring a grain of that particular q_val. This knowledge is tracked by looking at
				 * the q_val_arr which is an array of boolean flags, one for each value of q_val, set when a baby thread measuring
				 * area of a grain of that q_val is fired and reset when the baby such a thread exits.
				 */
				long cum_pass_time = 0;
				int cum_thread_counter = 0;
				do {
					long st_time = 0;

					if (debug) {
						st_time = System.currentTimeMillis();
					}
					ExecutorService grains_pool = Executors.newFixedThreadPool(max_q);
					another_pass_to_do = false;
					pass_counter++;
					no_of_threads_in_this_pass = 0;
					/*
					 * These variables are sub-part of debug - they are used to control when a message is to be printed
					 */
					long debug_start_time = 0;
					long debug_last_print_time = 0;
					int debug_last_print_thread_counter = 0;
					if (debug) {
						debug_start_time = System.currentTimeMillis();
					}
					//Now we start the main scan

					for (short row = 1; row < ARR_LIM; row++) {		//Now start the scan of the state matrix
						for (short col = 1; col < ARR_LIM; col++) {
							q_val = state_matrix_copy[row][col];			//Read the q_val of the current row,col element
							if (q_val <= IMM) {						//Ignore if its already under processing, or is an impurity
								continue;
							}
							another_pass_to_do = true;
							if (flag_array[q_val - 1] == false) {		//Fire new thread, as there is no running thread for this q_val
								no_of_threads_in_this_pass++;
								flag_array[q_val - 1] = true;			//This flag is reset by the thread

								/*
								 * This block is only for debugging and speed optimization
								 */
								if ((debug) && (no_of_threads_in_this_pass > (debug_last_print_thread_counter + state_size * 10))) {
									//This is printed only after state_size*10 number of threads, as this printing is expensive process
									//and that also only after every 5 minutes (300,000 miliseconds)
									long debug_end_time = System.currentTimeMillis();
									if ((debug_end_time - debug_start_time) > (debug_last_print_time + 30000)) {
										int debug_not_processed = 0;
										int debug_total_accessed = 0;
										for (short i = 1; i <= row; i++) {
											for (short j = 1; j <= col; j++) {
												if (state_matrix_copy[i][j] > IMM) {
													debug_not_processed++;
												}
												if (state_matrix_copy[i][j] != IMM) {
													debug_total_accessed++;
												}
											}
										}
										double debug_pass_efficiency = 100.0 - (double) (debug_not_processed * 100) / ((double) (debug_total_accessed));
										System.out.println("Debug: Grain area thead: " + no_of_threads_in_this_pass + " with pass efficiency: " + debug_pass_efficiency + " in pass: " + pass_counter + " in cum time: " + (debug_end_time - debug_start_time) + " when no of grains were : " + total_grains);
										debug_last_print_time = debug_end_time - debug_start_time;
										debug_last_print_thread_counter = no_of_threads_in_this_pass;
									}
								}

								aGrain new_grain = new aGrain(total_grains + 1, q_val, row, col);
								Runnable the_runs = new find_area(new_grain, false);		//These are not click processing calculations
								grains_pool.execute(the_runs);
								total_grains++;
							} else {
								flag_array_missed_counter++;
								if (flag_array_missed_counter > 5000) {
									try {
										Thread.sleep(1);
									} catch (InterruptedException e) {
									}
									flag_array_missed_counter = 0;
								}
							}
						}
					}// This would mean all max_q threads are fired, and the entire matrix has been scanned once.
					grains_pool.shutdown();
					while (!grains_pool.isTerminated()) {										//Now we wait till all threads come home, and take another pass
					}
					/*
					 * This again is used only when debugging and optimizing
					 */
					if (debug) {
						int debug_not_processed = 0;
						int debug_total_accessed = 0;
						for (short i = 1; i <= ARR_LIM; i++) {
							for (short j = 1; j <= ARR_LIM; j++) {
								if (state_matrix_copy[i][j] > IMM) {
									debug_not_processed++;
								}
								if (state_matrix_copy[i][j] != IMM) {
									debug_total_accessed++;
								}
							}
						}
						long debug_end_time = System.currentTimeMillis();
						cum_thread_counter += no_of_threads_in_this_pass;
						cum_pass_time += (debug_end_time - st_time);
						double debug_pass_efficiency = 100.0 * (1.0 - (double) (debug_not_processed) / ((double) (debug_total_accessed)));
						System.out.println("Pass: " + pass_counter + " no of threads: " + no_of_threads_in_this_pass + " at efficiency: " + fmt_double.format(debug_pass_efficiency) + "% time: " + (debug_end_time - st_time) + " cum threads: " + cum_thread_counter + " cum time: " + cum_pass_time);
					} //End of if (debug)
				} while (another_pass_to_do);

				dout_grain_list.close();
				//Once the whole matrix has been analyzed, all numbers would have become negative, so we restore them to positve
				for (short i = 1; i < ARR_LIM; i++) {
					for (short j = 1; j < ARR_LIM; j++) {
						if (state_matrix_copy[i][j] < IMM) {
							state_matrix_copy[i][j] = (short) ((-1) * state_matrix_copy[i][j]);
						}
					}
				}
				/*
				 * If a grain has been clicked, we run this computation. Please keep in mind that the mouse_x, and mouse Y follow a
				 * different convention than array row col, so row is mouse_Y, and col is mouse_X
				 */
				if ((click_set) && (click_processed == false) && ((mouse_x > 0) || (mouse_y > 0))) {
					aGrain click_grain = new aGrain(0, state_matrix_copy[mouse_y][mouse_x], mouse_y, mouse_x);
					Runnable click_run = new find_area(click_grain, true);
					Thread click_thread = new Thread(click_run);
					click_thread.start();
					while (!click_processed) {			//This flag is set by the click_thread.
						try {
							Thread.sleep(1);
						} catch (InterruptedException e) {
						}
					}
					for (short i = 1; i < ARR_LIM; i++) {
						for (short j = 1; j < ARR_LIM; j++) {
							if (state_matrix_copy[i][j] < IMM) {
								state_matrix_copy[i][j] = (short) ((-1) * state_matrix_copy[i][j]);
							}
						}
					}
					when_click_processed = System.currentTimeMillis();
				}
				/*
				 * This section generates the overall statistics for the run. The flag in_saving stats prevents the thread that is
				 * updating the screen from reading these variables as it updates.
				 */
				hamil_at_last_save = compute_hamil_val(state_matrix_copy);
				in_saving_stats = true;
				time_at_last_save = System.currentTimeMillis();
				total_grains_at_last_save = total_grains;
				avg_area_at_last_save = (double) ((int) (100.0 * (double) (state_size * state_size - impurity_count) / (double) (total_grains))) / (double) (100.0);
				for (short i = 0; i < 7; i++) {
					for (short j = 0; j < MAX_LIST; j++) {
						big_grains_list_at_last_save[i][j] = big_grains_list[i][j];
					}
				}
				in_saving_stats = false;
				try {
					print_array(file_save_cntr);		//Complete the binary dump of the array, then prints the image file, and prints the grains list
				} catch (IOException i) {
				}
				if (debug) {
					System.out.printf("File: %2d Iter: %d Run time (in secs): %d Tot grn: %d  avg ar: %.3f Hamil: %d xch: %d th_flips: %d\n", file_save_cntr, mcs_no, (time_at_last_save - run_start_time) / 1000, total_grains, ((double) (state_size * state_size - impurity_count) / (double) (total_grains)), hamil_at_last_save, flip_counter, thermal_flips);
				}
				file_save_cntr++;
				first_file_save_cntr = true;
				free_to_compute = true;
			} while (true); //End of the infinite do loop
		} //End of thread compute_area run()

		private void print_array(short when) throws IOException {
			/*
			 * This method writes out the data matrix, its state size, its guard rows, and the impurity count, and impurity shapes,
			 * and value of kT, the Hamiltonian, the number of flips since start, and number of thermal flips since start in a
			 * binary file.
			 */
			DataOutputStream dout_dat = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(user_dir + "_Grains_matrix_" + when + ".dat")));

			dout_dat.writeShort(when);
			dout_dat.writeShort(state_size);
			dout_dat.writeShort(max_q);
			dout_dat.writeLong(hamil_at_last_save);
			dout_dat.writeBoolean(periodic);
			dout_dat.writeBoolean(modified);
			dout_dat.writeDouble(prop_for_T);
			dout_dat.writeInt(impurity_count);
			dout_dat.writeShort(impurity_shape);
			dout_dat.writeLong(exchgs_at_last_save);
			dout_dat.writeLong(thermal_exchgs_at_last_save);
			dout_dat.writeInt(prev_no_of_mcs + iter_at_last_save);
			dout_dat.writeInt(total_grains);
			dout_dat.writeShort(MAX_LIST);
			dout_dat.writeLong(ini_hamil);

			for (short i = 0; i < BASE; i++) {			//Write including the two guard rows
				for (short j = 0; j < BASE; j++) {
					dout_dat.writeShort(state_matrix_copy[i][j]);
				}
			}
			for (short i = 0; i < 7; i++) {
				for (short j = 0; j < MAX_LIST; j++) {
					dout_dat.writeLong(big_grains_list_at_last_save[i][j]);
				}
			}
			dout_dat.close();
			PrintWriter dout_txt = new PrintWriter(user_dir + "_Grains_data_" + when + ".txt");
			dout_txt.println("File Reference Number: " + when);
			dout_txt.println("state_size: " + state_size);
			dout_txt.println("max_q value: " + max_q);
			dout_txt.println("Flag for periodic nature:" + periodic);
			dout_txt.println("Flag for modified replacement: " + modified);
			dout_txt.println("Value for thermal propensity: " + prop_for_T);
			dout_txt.println("Total Impurity Count: " + impurity_count);
			dout_txt.println("Shape of impurities: " + impurity_shape);
			dout_txt.println("Value of Hamiltonian: " + hamil_at_last_save);
			dout_txt.println("Total number of exchanges :" + exchgs_at_last_save);
			dout_txt.println("Total number of thermal flips: " + thermal_exchgs_at_last_save);
			int temp = prev_no_of_mcs + iter_at_last_save;
			dout_txt.println("Total number of cumulative MCS steps: " + temp);
			dout_txt.println("Total number of grains: " + total_grains_at_last_save);
			dout_txt.println("Average grain size : " + fmt_double.format(avg_area_at_last_save));
			dout_txt.println("Maximum area grain size: " + big_grains_list_at_last_save[3][0]);
			dout_txt.println("Perimeter of grain with maximum area: " + big_grains_list_at_last_save[4][0]);
			dout_txt.println("q value of grain with maximum area: " + big_grains_list_at_last_save[0][0]);
			dout_txt.println("Initial Hamiltonian of this series of runs: " + ini_hamil);
			long now_time = System.currentTimeMillis();
			dout_txt.println("This file has been saved after " + (now_time - run_start_time) / 1000 + " secs from start.");
			dout_txt.close();

			BufferedImage image = new BufferedImage(state_size, state_size, BufferedImage.TYPE_INT_ARGB);
			WritableRaster raster = image.getRaster();
			ColorModel model = image.getColorModel();

			for (int i = 1; i < ARR_LIM; i++) {
				for (int j = 1; j < ARR_LIM; j++) {
					short q_val = state_matrix[i][j];
					Color shade = new Color(colours[q_val]);
					Object exact_shade = model.getDataElements(shade.getRGB(), null);	//convert the colour into Object form
					raster.setDataElements(i - 1, j - 1, exact_shade);						//set the pixel into the exact shade
				}
			}
			File png_output = new File(user_dir + "_Grains_image_" + when + ".png");
			ImageIO.write(image, "PNG", png_output);
			/*
			 * Hamiltonians are saved in one cumulative file, so that they can be easily plotted. Also for same logic, we do NOT
			 * print Hamiltonian of the initial runin long_analysis. We print it here, at start of this thread, and then cumulate
			 * into same thread.
			 */
			try {
				PrintWriter dout_hamil = new PrintWriter(new BufferedWriter(new FileWriter(user_dir + "_Hamil.csv", true)));
				temp = prev_no_of_mcs + iter_at_last_save;
				dout_hamil.println(temp + "," + hamil_at_last_save + "," + exchgs_at_last_save + "," + thermal_exchgs_at_last_save + "," + total_grains_at_last_save + "," + fmt_double.format(avg_area_at_last_save));
				dout_hamil.close();		//This ensures that even if the run is terminated in before closure, Hamiltonian is saved
			} catch (IOException e) {
			}
			return;
		} //End of method print_array
	} //End of class compute__area

	public static class find_area implements Runnable {

		private int unprocessed = 0;
		private int processed = 0;
		private boolean still_to_process = true;							//This flag controls the queue processing
		private long area = 0;
		private long perim = 0;
		private short curr_row;
		private short curr_col;
		private short q_val;
		private short ini_row;
		private short ini_col;
		private aGrain thisgrain;
		private int tot_imp;
		private int belly_imp;
		private boolean to_process_click;

		public find_area(aGrain the_grain, boolean to_process_a_click) {
			q_val = the_grain.get_q_val();
			curr_row = (short) (the_grain.get_address() / BASE);
			curr_col = (short) (the_grain.get_address() % BASE);
			ini_row = curr_row;
			ini_col = curr_col;
			thisgrain = the_grain;
			to_process_click = to_process_a_click;									//This flag determines if we are using it to process clicks or not
		}

		@Override
		public void run() {

			unprocessed = 0;
			processed = 0;
			still_to_process = true;							//This flag controls the queue processing
			area = 0L;
			perim = 0;

			int[] queue = new int[q_area[q_val - 1] + 1];
			boolean[] que_st = new boolean[q_area[q_val - 1] + 1];
			int[] queue_perim = new int[q_area[q_val - 1] + 1];		//This queue will store all perimeter element queue
			int[] impurity_queue = new int[impurity_count];

			queue[0] = BASE * curr_row + curr_col;							//Initialize the queue by storing the current starting address
			que_st[0] = false;
			dir_vectors dir = new dir_vectors();				//generate the array of control indices for computing immediate neighbourhood
			queue_perim[0] = BASE * curr_row + curr_col;
			perim = 1;

			do {

				//We take the starting cell of the grain, find all matching neighbours, and then for each neighbour so found,
				//we check if its already in the queue or not.
				//If not, then insert it in increasing order (keeps the queue array sorted, and increase the unprocessed variable (this
				//becomes eqvt to queue size).
				//We now proceed to locate all neighbours of the given input cell.
				boolean is_on_grain_edge = dir.set_val(curr_row, curr_col);		//we get the direction vectors from the current cell (range -1 to 1)

				for (short x = dir.get_st_val_i(); x <= dir.get_end_val_i(); x++) {	//we look at neighbouring cells for matching cells
					for (short y = dir.get_st_val_j(); y <= dir.get_end_val_j(); y++) {
						if ((x == 0) && (y == 0)) {
							continue;							//dont count yourself as your own neighbour, nor can oneself be an impurity
						}
						if (state_matrix_copy[curr_row + x][curr_col + y] == IMM) {
							boolean found = false;
							int new_imp = (curr_row + x) * BASE + (curr_col + y);
							for (int z = 0; z < tot_imp; z++) {
								if (impurity_queue[z] == new_imp) {
									found = true;
								}
							}
							if (!(found)) {
								impurity_queue[tot_imp] = new_imp;
								tot_imp++;
							}
						} else {
							if (state_matrix_copy[curr_row + x][curr_col + y] == q_val) {		//if there is a neighbouring cell matching our q_val
								int new_entry = (BASE * (curr_row + x)) + (curr_col + y);	//new entry into the queue,to be inserted in a sorted manner
								//the queue contains "unprocessed" no of elements
								boolean found = false;								//this flag tracks if this neighbour has already been put in queue
								int where = 0;										//this will point to where to insert the new_entry in the queue
								for (int z = 0; z < unprocessed; z++) {
									if (queue[z] == new_entry) {
										found = true;								//this one already exists in queue - so ignore this neighbour
									}
									if (queue[z] < new_entry) {
										where++;
									}
								}
								if (found) {
									continue;										//this neighbour has already been inserted into the array
								} else {
									//We push all elements from (where+1) till unprocessed by one place, and insert this new element in the gap
									for (int z = unprocessed; z > where; z--) {
										queue[z] = queue[z - 1];					//move the addresses of the neighbours in the queue
										que_st[z] = que_st[z - 1];					//move the flags representing the processing state also
									}
									if (where <= processed) {
										processed++;								//Processed points to the current location, so update that too
									}
									//System.out.println("Entering element "+new_entry+" at "+where);
									queue[where] = new_entry;						//Insert new entry made into the queue
									que_st[where] = false;							//Set new entry processing state as false-obviously not yet processed
									unprocessed++;									//Increase the size of the queue
								}
							}  //End of loop when a matching neighbour is found, and inserted into the queue
						}
					} //End of for loop
				} //End of for loops to test all neighbours.
				/*
				 * The first part of the algorithm is over - we have added to the queue all such neighbours that are of same q_val
				 * as the given cell, ensuring they are inserted in a sorted manner, and are NOT duplicated.
				 *
				 * Now we commence the second part, where we process the current queue entry for area. We also negate the q_entry,
				 * so that its not double counted in the area computation.
				 */
				boolean is_found = false;
				for (int k = 0; k < perim; k++) {
					if (queue_perim[k] == (curr_row * BASE + curr_col)) {
						is_found = true;
					}
				}
				if (!(is_found)) {
					queue_perim[(int) (perim)] = curr_row * BASE + curr_col;
					perim++;
				}
				que_st[processed] = true;
				area++;							//current cell is accounted for.
				state_matrix_copy[curr_row][curr_col] = (short) ((-1) * q_val);

				//Now we scan the whole queue to find the first "unprocessed element" and do this loop again. If no such element is left, then
				//this grain is over, we reset the still_to_process flag, and gracefully proceed to the computation of perimeter..
				boolean found_unproc = false;
				for (processed = 0; processed < unprocessed; processed++) {
					if (que_st[processed] == false) {
						found_unproc = true;
						break;
					}
				}
				if (found_unproc) {
					int addr_to_process = queue[processed];
					curr_row = (short) (addr_to_process / BASE);		//convert the address stored in queue back to row,col format
					curr_col = (short) (addr_to_process % BASE);
				} else {
					still_to_process = false;							//there are no unprocessed queue entries left, so exit the while loop
				}
			} while (still_to_process);

			/*
			 * Now we begin the second pass along the grain. We reset all grains status to false (this is just to reuse the memory,
			 * otherwise we would need another array of status flags corresponding to the perimeter queue) and then proceed to
			 * analyze the queue_perim sequence - this list contains unique addresses within the grains, that have at least ONE
			 * neighbour with a q_val not equal to theirs, excluding the guard rows/columns
			 */
			for (int z = 0; z < perim; z++) {
				curr_row = (short) (queue_perim[z] / BASE);
				curr_col = (short) (queue_perim[z] % BASE);
				if ((state_matrix_copy[curr_row][curr_col + 1] == (-1) * q_val)
					&& (state_matrix_copy[curr_row][curr_col - 1] == (-1) * q_val)
					&& (state_matrix_copy[curr_row + 1][curr_col] == (-1) * q_val)
					&& (state_matrix_copy[curr_row - 1][curr_col] == (-1) * q_val)
					&& (state_matrix_copy[curr_row + 1][curr_col + 1] == (-1) * q_val)
					&& (state_matrix_copy[curr_row + 1][curr_col - 1] == (-1) * q_val)
					&& (state_matrix_copy[curr_row - 1][curr_col + 1] == (-1) * q_val)
					&& (state_matrix_copy[curr_row - 1][curr_col - 1] == (-1) * q_val)) {
					perim--;
				}
			}
			for (int i = 0; i < tot_imp; i++) {
				curr_row = (short) (impurity_queue[i] / BASE);
				curr_col = (short) (impurity_queue[i] % BASE);
				if (((state_matrix_copy[curr_row][curr_col + 1] == (-1) * q_val) || (state_matrix_copy[curr_row][curr_col + 1] == IMM))
					&& ((state_matrix_copy[curr_row][curr_col - 1] == (-1) * q_val) || (state_matrix_copy[curr_row][curr_col - 1] == IMM))
					&& ((state_matrix_copy[curr_row + 1][curr_col] == (-1) * q_val) || (state_matrix_copy[curr_row + 1][curr_col] == IMM))
					&& ((state_matrix_copy[curr_row - 1][curr_col] == (-1) * q_val) || (state_matrix_copy[curr_row - 1][curr_col] == IMM))
					&& ((state_matrix_copy[curr_row + 1][curr_col + 1] == (-1) * q_val) || (state_matrix_copy[curr_row + 1][curr_col + 1] == IMM))
					&& ((state_matrix_copy[curr_row + 1][curr_col - 1] == (-1) * q_val) || (state_matrix_copy[curr_row + 1][curr_col - 1] == IMM))
					&& ((state_matrix_copy[curr_row - 1][curr_col + 1] == (-1) * q_val) || (state_matrix_copy[curr_row - 1][curr_col + 1] == IMM))
					&& ((state_matrix_copy[curr_row - 1][curr_col - 1] == (-1) * q_val) || (state_matrix_copy[curr_row - 1][curr_col - 1] == IMM))) {
					belly_imp++;
				}
			}
			/*
			 * If we have been called to process a click, then we need not do all the saving into grain list etc.
			 */
			if (to_process_click) {
				click_q_val = q_val;
				click_area = area;
				click_perim = perim;
				click_total_imp = tot_imp;
				click_imp_in_belly = belly_imp;
				click_processed = true;
				return;
			} else {
				thisgrain.add_area(area);
				thisgrain.add_perim(perim);
				thisgrain.add_imp_total(tot_imp);
				thisgrain.add_imp_in_belly(belly_imp);

				update_stats u = new update_stats();
				u.update_stats(q_val, ini_row, ini_col, area, perim, tot_imp, belly_imp);
				print_grain_list p = new print_grain_list();
				p.print_grain(thisgrain);
				flag_array[q_val - 1] = false;
			}	//end of else of to_process_click
			return;
		} //End of method call
	}//End of class find_area

	public static class update_stats {
		/*
		 * This has to be written as a re-entrant synchronized code, as many grains would be accessing the variables, max, min, etc.
		 */

		public update_stats() {
			return;
		}

		synchronized void update_stats(short q_val, short row, short col, long area, long perim, long tot_imp, long imp_in_belly) {
			/*
			 * This method will scan the top MAX_DISPLAY array of big_grains_list, and addd this grain to that list, if so
			 * qualified.
			 */
			long curr_min = big_grains_list[3][MAX_LIST - 1];
			if (area > curr_min) {						//Only then it makes sense to add to toppers list
				short loc_index = 0;
				for (; loc_index < MAX_LIST; loc_index++) {
					if (big_grains_list[3][loc_index] >= area) {
						continue;
					} else {
						break;
					}
				}
				if (loc_index < MAX_LIST) {
					for (short i = (short) (MAX_LIST - 2); i >= loc_index; i--) {
						for (short j = 0; j < 7; j++) {
							big_grains_list[j][i + 1] = big_grains_list[j][i];
						}
					}
					big_grains_list[0][loc_index] = (long) (q_val);
					big_grains_list[1][loc_index] = (long) (row);
					big_grains_list[2][loc_index] = (long) (col);
					big_grains_list[3][loc_index] = (long) (area);
					big_grains_list[4][loc_index] = (long) (perim);
					big_grains_list[5][loc_index] = (long) (tot_imp);
					big_grains_list[6][loc_index] = (long) (imp_in_belly);
				}
			}
			notifyAll();
		}
	}

	public static class print_grain_list {

		public print_grain_list() {
			return;
		}

		synchronized void print_grain(aGrain gr) {
			dout_grain_list.println(Integer.toString(gr.get_seq()) + "," + Short.toString(gr.get_q_val()) + "," + Short.toString(gr.get_row()) + "," + Short.toString(gr.get_col()) + "," + Long.toString(gr.get_area()) + "," + Long.toString(gr.get_perim()) + "," + Integer.toString(gr.get_imp_in_belly()) + "," + Integer.toString(gr.get_imp_total() - gr.get_imp_in_belly()));
			notifyAll();
		}
	}

	public static class Split_matrix implements Runnable {

		/*
		 * First, we copy those "global" variables into local private versions, so that their references need not be locked -
		 * otherwise the threads will be permanently locked.
		 */
		private int thr_id;
		private short lt_lim;
		private short rt_lim;
		private short tp_lim;
		private short bt_lim;
		private short STATE_SIZE_PART = (short) (state_size / MAT_SPLIT_SIZE);
		private int trial_no;
		private short[][] pvt_iesm = new short[3][3];
		private short hamil_1;										//These variables contain the existing values of hamiltonian
		private short hamil_2;										//and new computes of the hamiltonian
		private short ex_val;

		public Split_matrix(int thread_no) {
			/*
			 * The logic here enforces a uniform number of trials within a quadrant, that is if the whole matrix were to have
			 * randomly generated trial attempts, it would have been possible that theber of trials in each quadrant would not be
			 * same in one iteration, but over 30 iterations and above the difference in number (max-min) is 2, which is
			 * insignificant to 10000*10000 trails per iteration, running for 100000 iterations.
			 */
			trial_no = TRIALS / MAX_MAT_THREADS;
			thr_id = thread_no;
			lt_lim = (short) (1 + (thr_id % MAT_SPLIT_SIZE) * STATE_SIZE_PART);
			rt_lim = (short) (lt_lim + STATE_SIZE_PART);
			tp_lim = (short) (1 + (thr_id / MAT_SPLIT_SIZE) * STATE_SIZE_PART);
			bt_lim = (short) (tp_lim + STATE_SIZE_PART);
		}

		@Override
		public void run() {
			/*
			 * Implements the flip algorithm as provided by Prof. K R Phaneesh
			 */
			Random rand_gen = new Random();

			do {
				//generate the random element index position
				short rand_row = (short) (lt_lim + rand_gen.nextInt(state_size / MAT_SPLIT_SIZE)); //Since we are attacking by max_thread quadrants
				short rand_col = (short) (tp_lim + rand_gen.nextInt(state_size / MAT_SPLIT_SIZE)); //we generate random locations within quadrants

				if (state_matrix[rand_row][rand_col] == IMM) {
					if (debug) {
						debug_xchg_failures[thr_id]++;
					}
					continue;
				}
				//If the frequency is being measured, else keep in comments
				frequency[rand_row - 1][rand_col - 1]++;
				//
				for (short x = 0; x <= 2; x++) {								//Copy the IESM matrix around rand_row, rand_col values
					for (short y = 0; y <= 2; y++) {
						pvt_iesm[x][y] = state_matrix[rand_row + x - 1][rand_col + y - 1];
					}
				}
				ex_val = state_matrix[rand_row][rand_col];					//The existing value of the q_val
				hamil_1 = kron(pvt_iesm);										//The intial uncorrected Hamiltonian value
				short flip_grain;
				if (!modified) {
					flip_grain = (short) (1 + rand_gen.nextInt(max_q));		//consider a replacement q_val between 1 to max_q (both incl)
				} else {											//We take a random neighbourhood, and then populate from that location
					do {
						int new_loc_x = rand_gen.nextInt(3);
						int new_loc_y = rand_gen.nextInt(3);			//guarantees to be one of the neighbours, randomly chosen.
						if (pvt_iesm[new_loc_x][new_loc_y] == IMM) {	//but not an impurity
							continue;
						}
						flip_grain = state_matrix[rand_row + new_loc_x - 1][rand_col + new_loc_y - 1];
						break;
					} while (true);
				}
				if (ex_val == flip_grain) {									//ignore this trial if its same as existing value
					if (debug) {
						debug_xchg_success[thr_id]++;
					}
					trial_no--;
					continue;
				}
				pvt_iesm[1][1] = flip_grain;									//We replace the value, or flip the grain
				hamil_2 = kron(pvt_iesm);										//The after flip Hamiltonian value is recomputed.
				if (hamil_2 <= hamil_1) {
					flips[thr_id]++;										//This flip is accepted, in general
					state_matrix[rand_row][rand_col] = flip_grain;
					if (set_tracker) {
						tracker_buffer[thr_id][0][tracker_index[thr_id]] = rand_row;
						tracker_buffer[thr_id][1][tracker_index[thr_id]] = rand_col;
						tracker_buffer[thr_id][2][tracker_index[thr_id]] = ex_val;
						tracker_buffer[thr_id][3][tracker_index[thr_id]] = flip_grain;
						tracker_index[thr_id]++;
					}
				} else {
					if ((prop_for_T > 0) && (hamil_2 > hamil_1)) {
						//We generate the value of exp{(H2-H1)/kT} and then generate P
						double p_value = Math.exp((-1) * ((hamil_2 - hamil_1) / prop_for_T));		//The corrected value of the thermal flip
						double r_val = rand_gen.nextDouble();
						if (p_value > r_val) {
							state_matrix[rand_row][rand_col] = flip_grain;
							th_flips[thr_id]++;
							if (set_tracker) {
								tracker_buffer[thr_id][0][tracker_index[thr_id]] = rand_row;
								tracker_buffer[thr_id][1][tracker_index[thr_id]] = rand_col;
								tracker_buffer[thr_id][2][tracker_index[thr_id]] = ex_val;
								tracker_buffer[thr_id][3][tracker_index[thr_id]] = flip_grain;
								tracker_index[thr_id]++;
							}
						} else { //This else arises only when there is a debug on - tracks trial failures
							if (debug) {
								debug_xchg_failures[thr_id]++;
							}
						}
					}
				}
				//If the flipped value happened to be on edges, then for mirrored edges, we change the guard columns accordingly...
				if ((periodic) && ((rand_row == 1) || (rand_col == 1) || (rand_row == state_size) || (rand_col == state_size))) {
					if (rand_row == 1) {
						state_matrix[ARR_LIM][rand_col] = flip_grain;
					} else {
						if (rand_row == state_size) {
							state_matrix[0][rand_col] = flip_grain;
						}
					}
					if (rand_col == 1) {
						state_matrix[rand_row][ARR_LIM] = flip_grain;
					} else {
						if (rand_col == state_size) {
							state_matrix[rand_row][0] = flip_grain;
						}
					}
				}
				if (debug) {
					debug_xchg_success[thr_id]++;
				}
				trial_no--;
			} while (trial_no > 0); //End of for loop of n^2 trials
			return;
		} //End of class run

		short kron(short[][] iesm) {
			/*
			 * Computes the kronecker delta of the iesm matrix, but returns the hamiltonian (8-sum(kronecker delta));
			 */
			short kron_val = 0;
			for (short x = 0; x <= 2; x++) {
				for (short y = 0; y <= 2; y++) {
					if (iesm[x][y] == iesm[1][1]) {
						kron_val++;
					}
				}
			}
			kron_val--; //We test all nine times in the loop above, but we should not do a self compare, so we decrease
			return ((short) (8 - kron_val));
		}
	} //End of class Runnable of state_matrix

	public static class make_impurities {

		/*
		 * The standard algorithm for generating impurities of different shapes is that we first allocate the variable absolute
		 * size. This size is minimum size, and then is replaced by a larger size of random growth pattern has been indicated. Once
		 * that is done, we take a random point for creating the impurity. In specific shapes, where the images are NOT symmetrical,
		 * we also randomly generate an orientation value, 0 for H, 1 for V Then we call check_possibility, to assess three things,
		 * given the orientation, is it possible to draw a rectangle of the required size (using abs_value as the measurement
		 * driver, and shape determing the other size aspect), which is within crystal boundaries, and does not overlap another
		 * impurity, and does not enclose an existing impurity.
		 */
		public make_impurities() {
			return;
		}

		public int imp_shape_0() {	//creates impurities of squares of diiferent sizes, default 1x1, but with random_size=true upto 10x10
			short abs_size = 1;
			if (random_size) {
				abs_size = (short) (abs_size + rand_gen.nextInt((int) (max_rand_size)));
			}
			short rand_row = (short) (1 + rand_gen.nextInt((int) (state_size)));
			short rand_col = (short) (1 + rand_gen.nextInt((int) (state_size)));
			/*
			 * Allots a 3 sized array containing the direction of the growth of the impurity in x, y, and orientation between x and
			 * y
			 */
			short[] dirn = new short[2];
			if (!(check_possibility(rand_row, rand_col, abs_size, abs_size, (short) (0), dirn))) {
				return (0);					//Not possible to set this shape of impurity at this given rand row/col and size
			}
			if (state_matrix[rand_row][rand_col] == IMM) {
				return (0);
			}
			//Once the square allotment area has been checked,, we proceed to allot the impurities
			for (short x = 0; x < abs_size; x++) {
				for (short y = 0; y < abs_size; y++) {
					state_matrix[rand_row + (dirn[0]) * x][rand_col + (dirn[1]) * y] = IMM;
				}
			}
			return (abs_size * abs_size);
		}

		public int imp_shape_1() { //creates impurities of rhombuses of diiferent sizes, default 13531 (size=5), but with random_size=true larger
			short abs_size = 5;
			int ar = 0;
			if (random_size) {
				abs_size = (short) (abs_size + rand_gen.nextInt((int) (max_rand_size)));
				if ((abs_size % 2) == 0) {
					abs_size += 1;									//For this shape we dont accept even-sized square sizes
				}
			}
			short rand_row = (short) (1 + rand_gen.nextInt((int) (state_size)));
			short rand_col = (short) (1 + rand_gen.nextInt((int) (state_size)));

			short[] dirn = new short[2];
			if (!(check_possibility(rand_row, rand_col, abs_size, abs_size, (short) (0), dirn))) {
				return (0);					//Not possible to set this shape of impurity at this given rand row/col and size
			}
			//Once the square allotment area has been checked, we proceed to allot the impurities
			//In this case, we first start with top left of the array, which, if dirn[0] is negative is computed
			rand_row = (dirn[0] < (short) (0)) ? (short) (rand_row - abs_size) : rand_row;
			rand_col = (dirn[1] < (short) (0)) ? (short) (rand_col - abs_size) : rand_col;
			int mp = (abs_size - 1) / 2;
			for (int i = rand_row; i < rand_row + mp + 1; i++) {
				for (int j = rand_col + (mp - (i - rand_row)); j <= rand_col + (mp + (i - rand_row)); j++) {
					state_matrix[i][j] = IMM;
					ar++;
				}
			}
			for (int i = rand_row + mp + 1; i < rand_row + abs_size; i++) {
				for (int j = rand_col + ((i - rand_row) - mp); j < rand_col + mp + (abs_size - (i - rand_row)); j++) {
					state_matrix[i][j] = IMM;
					ar++;
				}
			}
			return (ar);
		}

		public int imp_shape_2() { ////rectangles of size 4x2, size randomly increasable to any nx(n-2)
			short abs_size = 4;
			if (random_size) {
				abs_size = (short) (abs_size + rand_gen.nextInt((int) (max_rand_size)));
			}
			short rand_row = (short) (1 + rand_gen.nextInt((int) (state_size)));
			short rand_col = (short) (1 + rand_gen.nextInt((int) (state_size)));
			short[] dirn = new short[2];	//Allots a 2 sized array containing the direction of the growth of the impurity

			//Now for this shape, there is a distinct orientation difference, so we generate a random number between 0 and 1, and
			//for 0, we set orientation a horizontal, and 1 as vertical. If we wish to fix the orientation, set this to 0 or 1 as needed
			short orient = (rand_gen.nextDouble() < 0.5 ? (short) (0) : (short) (1));

			if (!(check_possibility(rand_row, rand_col, abs_size, (short) (abs_size - 2), orient, dirn))) {
				return (0);					//Not possible to set this shape of impurity at this given rand row/col and size
			}
			if (state_matrix[rand_row][rand_col] == IMM) {
				return (0);
			}
			if (orient == 0) {
				for (short x = 0; x < abs_size; x++) {
					for (short y = 0; y < (abs_size - 2); y++) {
						state_matrix[rand_row + (dirn[0]) * x][rand_col + (dirn[1]) * y] = IMM;
					}
				}
			} else {
				for (short x = 0; x < (abs_size - 2); x++) {
					for (short y = 0; y < abs_size; y++) {
						state_matrix[rand_row + (dirn[0]) * x][rand_col + (dirn[1]) * y] = IMM;
					}
				}
			}
			return (abs_size * (abs_size - 2));
		}

		public int imp_shape_3() { //Needles of thickness 1 and length 2, randmly increasable to n
			short abs_size = 2;
			if (random_size) {
				abs_size = (short) (2 + rand_gen.nextInt((int) (max_rand_size)));
			}
			short rand_row = (short) (1 + rand_gen.nextInt((int) (state_size)));
			short rand_col = (short) (1 + rand_gen.nextInt((int) (state_size)));
			short[] dirn = new short[2];	//Allots a 2 sized array containing the direction of the growth of the impurity
			short orient = (rand_gen.nextDouble() < 0.5 ? (short) (0) : (short) (1));
			if (!(check_possibility(rand_row, rand_col, (short) (1), abs_size, orient, dirn))) {
				return (0);					//Not possible to set this shape of impurity at this given rand row/col and size
			}
			if (state_matrix[rand_row][rand_col] == IMM) {
				return (0);
			}
			if (orient == 0) {
				for (short y = 0; y < abs_size; y++) {
					state_matrix[rand_row][rand_col + (dirn[1]) * y] = IMM;
				}
			} else {
				for (short x = 0; x < abs_size; x++) {
					state_matrix[rand_row + (dirn[0]) * x][rand_col] = IMM;
				}
			}
			return (abs_size);
		}

		public int imp_shape_4() { //Needles of thickness 3 and min length 5, tapered at ends
			short abs_size = 5;
			if (random_size) {
				abs_size = (short) (5 + rand_gen.nextInt((int) (max_rand_size)));
			}
			short rand_row = (short) (1 + rand_gen.nextInt((int) (state_size)));
			short rand_col = (short) (1 + rand_gen.nextInt((int) (state_size)));
			short[] dirn = new short[2];	//Allots a 2 sized array containing the direction of the growth of the impurity
			short orient = (rand_gen.nextDouble() < 0.5 ? (short) (0) : (short) (1));
			if (!(check_possibility(rand_row, rand_col, (short) (3), abs_size, orient, dirn))) {
				return (0);					//Not possible to set this shape of impurity at this given rand row/col and size
			}
			if (state_matrix[rand_row][rand_col] == IMM) {
				return (0);
			}
			if (orient == 0) {
				for (short x = 0; x < 3; x++) {
					for (short y = 1; y < abs_size - 1; y++) {
						state_matrix[rand_row + dirn[0] * x][rand_col + (dirn[1]) * y] = IMM;
					}
				}
				state_matrix[rand_row + dirn[0] * 1][rand_col] = IMM;				//Draw the needle tips :-)
				state_matrix[rand_row + dirn[0] * 1][rand_col + abs_size - 1] = IMM;
			} else {
				for (short x = 1; x < abs_size - 1; x++) {
					for (short y = 0; y < 3; y++) {
						state_matrix[rand_row + (dirn[0]) * x][rand_col + dirn[1] * y] = IMM;
					}
				}
				state_matrix[rand_row][rand_col + dirn[1] * 1] = IMM;				//Draw the needle tips :-)
				state_matrix[rand_row + abs_size - 1][rand_col + dirn[1] * 1] = IMM;
			}
			return ((abs_size - 2) * 3 + 2);
		}

		private boolean check_possibility(short row, short col, short x_size, short y_size, short orient, short[] dirn) {
			/*
			 * This is a common method to all the shape creators - it checks if the notionally rectangle box enveloping the max
			 * size+1 row/col on each direction for existing impurities, and returns false if any found, else returns true.
			 */
			if (orient == 0) {
				if ((row > (state_size - x_size - 1)) || (row < (1 + x_size))) {	//Impurity of this size cannot be implemented at this row
					return (false);
				}
				if ((col > (state_size - y_size - 1)) || (col < (1 + y_size))) {			// or column, so return.
					return (false);
				}
			} else {
				if ((row > (state_size - y_size - 1)) || (row < (1 + y_size))) {	//Impurity of this size cannot be implemented at this row
					return (false);
				}
				if ((col > (state_size - x_size - 1)) || (col < (1 + x_size))) {			// or column, so return.
					return (false);
				}
			}
			// Next, we check if the rectangle can be generated on the other direction (but same orientation)

			boolean already_imm = false;

			dirn[0] = 1;
			dirn[1] = 1;
			if (orient == 0) {
				if (row > (state_size - x_size - 1)) {
					dirn[0] = -1;
				}
				if (col > (state_size - y_size - 1)) {
					dirn[1] = -1;
				}
				for (short x = -1; x < x_size + 1; x++) {
					for (short y = -1; y < y_size + 1; y++) {
						if (state_matrix[row + (dirn[0]) * x][col + (dirn[1]) * y] == IMM) {
							already_imm = true;
						}
					}
				}
			} else {
				if (row > (state_size - y_size - 1)) {
					dirn[0] = -1;
				}
				if (col > (state_size - x_size - 1)) {
					dirn[1] = -1;
				}
				for (short x = -1; x < y_size + 1; x++) {
					for (short y = -1; y < x_size + 1; y++) {
						if (state_matrix[row + (dirn[0]) * x][col + (dirn[1]) * y] == IMM) {
							already_imm = true;
						}
					}
				}
			}
			if (already_imm) {
				return (false);
			}
			return (true);
		} //End of check_possibility method
	} //End of class make_impurities

	public static class aGrain {

		private int seq_c;
		private short q_val;
		private long area;
		private long perim;
		private short row;
		private short col;
		private int address;
		private int imp_in_belly;
		private int imp_total;
		//private String addr_label = "";

		public aGrain() {
		}

		public aGrain(int seq_no_given, short val_of_q, short row_no, short col_no) {
			q_val = val_of_q;
			area = 0;										//Initial value of the area
			seq_c = seq_no_given;								//Allot the given sequence number
			perim = 0;									//Initial value of the straight perimeter
			imp_total = 0;
			imp_in_belly = 0;
			address = row_no * BASE + col_no;
			row = row_no;
			col = col_no;
		} //End of the constructor

		public long add_area(long k) {
			area += k;
			return (area);
		}

		public long add_perim(long k) {
			perim += k;
			return (perim);
		}

		public int add_imp_in_belly(int k) {
			imp_in_belly += k;
			return (imp_in_belly);
		}

		public int add_imp_total(int k) {
			imp_total += k;
			return (imp_total);
		}

		public int get_seq() {
			return seq_c;
		}

		public short get_q_val() {
			return q_val;
		}

		public int get_address() {
			return (address);
		}

		public short get_row() {
			return (row);
		}

		public short get_col() {
			return (col);
		}

		public long get_area() {
			return (area);
		}

		public long get_perim() {
			return (perim);
		}

		public int get_imp_in_belly() {
			return (imp_in_belly);
		}

		public int get_imp_total() {
			return (imp_total);
		}
	}

	public static class long_area_analysis implements Runnable {

		NumberFormat fmt_double = new DecimalFormat("###,###,###,##0.000");
		short long_q_val;
		int long_total_grains;
		double long_grain_average;
		private int[] long_q_area = new int[max_q];
		ArrayList<aGrain> long_grain_list = new ArrayList<aGrain>();

		public long_area_analysis() {
			long_grain_list.ensureCapacity(1000);
			return;
		}

		@Override
		public void run() {
			in_long_analysis = true;
			long st_time = 0;
			if (debug) {
				st_time = System.currentTimeMillis();
			}
			/*
			 * We copy off the state_matrix, into a duplicate, expensive in memory terms, but takes off a major processing load and
			 * run time. The order of magnitude for very large matrices shows that the time to compute the area and grain list of
			 * initial matrix is about the same as the time to run 100,000 iterations !
			 */

			long_total_grains = 0;
			for (short i = 0; i < max_q; i++) {				//Build the frequency chart of the q_values distribution
				long_q_area[i] = 0;
			}
			for (short i = 1; i < ARR_LIM; i++) {
				for (short j = 1; j < ARR_LIM; j++) {
					if (long_state_matrix[i][j] == IMM) {
						continue;
					}
					long_q_area[long_state_matrix[i][j] - 1]++;
				}
			}

			for (short row = 1; row < ARR_LIM; row++) {		//Now start the scan of the state matrix
				for (short col = 1; col < ARR_LIM; col++) {
					long_q_val = long_state_matrix[row][col];			//Read the q_val of the current row,col element
					if (long_q_val <= IMM) {						//Ignore if its already under processing, or is an impurity
						continue;
					}
					aGrain new_grain = new aGrain(long_total_grains + 1, long_q_val, row, col);
					find_long_area f = new find_long_area(new_grain);
					f.compute_long_area();
					long_total_grains++;
					percent_ini_file_analysed = (100.0 * (row - 1) * state_size + (col - 1)) / (state_size * state_size);
				}
			}
			percent_ini_file_analysed = 100.0;
			for (short i = 1; i < ARR_LIM; i++) {
				for (short j = 1; j < ARR_LIM; j++) {
					if (long_state_matrix[i][j] < IMM) {
						long_state_matrix[i][j] = (short) ((-1) * long_state_matrix[i][j]);
					}
				}
			}
			if (debug) {
				long end_time = System.currentTimeMillis();
				System.out.println("Debug: Long total grains: " + long_total_grains + " in time: " + (end_time - st_time));
			}

			/*
			 * Now we save the outputs of this initial runs, once as .dat file, readable within this program, so that sequential
			 * sessions can be run, then as a text file containing the same data sets, but not the matrix. Finally, the matrix
			 * itself, as a png file encoded using the colormap.csv translation table.
			 */
			try {
				DataOutputStream dout_dat = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(user_dir + "_Grains_matrix_0.dat")));

				dout_dat.writeShort((short) (0));	//file counter
				dout_dat.writeShort(state_size);
				dout_dat.writeShort(max_q);
				dout_dat.writeBoolean(periodic);
				dout_dat.writeBoolean(modified);
				dout_dat.writeDouble(prop_for_T);
				dout_dat.writeInt(impurity_count);
				dout_dat.writeShort(impurity_shape);
				dout_dat.writeLong(0L);				//flip_counter
				dout_dat.writeLong(0L);				//thermal_flips
				dout_dat.writeInt(0);
				dout_dat.writeInt(long_total_grains);
				dout_dat.writeShort(MAX_DISPLAY);
				dout_dat.writeLong(ini_hamil);
				long_grain_average = (double) ((int) (100.0 * (double) (state_size * state_size - impurity_count) / (double) (long_total_grains))) / (double) (100.0);
				for (short i = 0; i < BASE; i++) {
					for (short j = 0; j < BASE; j++) {
						dout_dat.writeShort(long_state_matrix[i][j]);
					}
				}
				for (short i = 0; i < 7; i++) {
					for (short j = 0; j < BASE; j++) {
						dout_dat.writeLong(0L);				//largest grain list
					}
				}
				dout_dat.close();
				PrintWriter dout_txt = new PrintWriter(user_dir + "_Grains_data_0.txt");
				dout_txt.println("File Reference Number: 0");
				dout_txt.println("state_size: " + state_size);
				dout_txt.println("max_q: " + max_q);
				dout_txt.println("Flag for periodic nature:" + periodic);
				dout_txt.println("Flag for modified replacement: " + modified);
				dout_txt.println("Value for thermal propensity: " + prop_for_T);
				dout_txt.println("Total Impurity Count: " + impurity_count);
				dout_txt.println("Shape of impurities: " + impurity_shape);
				dout_txt.println("Total number of exchanges : 0");
				dout_txt.println("Total number of thermal flips: 0");
				dout_txt.println("Total number of cumulative MCS steps: 0");
				dout_txt.println("Total number of grains: " + long_total_grains);
				dout_txt.println("Average grain size : " + fmt_double.format(long_grain_average));
				dout_txt.println("Initial Hamiltonian of this series of runs: " + ini_hamil);
				long now_time = System.currentTimeMillis();
				dout_txt.println("This file has been saved after " + (now_time - run_start_time) / 1000 + " secs from start.");
				dout_txt.close();

			} catch (IOException i) {
			}

			BufferedImage image = new BufferedImage(state_size, state_size, BufferedImage.TYPE_INT_ARGB);
			WritableRaster raster = image.getRaster();
			ColorModel model = image.getColorModel();

			for (int i = 1; i < ARR_LIM; i++) {
				for (int j = 1; j < ARR_LIM; j++) {
					short q_val = long_state_matrix[i][j];
					Color shade = new Color(colours[q_val]);
					Object exact_shade = model.getDataElements(shade.getRGB(), null);	//convert the colour into Object form
					raster.setDataElements(i - 1, j - 1, exact_shade);						//set the pixel into the exact shade
				}
			}
			try {
				File png_output = new File(user_dir + "_Grains_image_0.png");
				ImageIO.write(image, "png", png_output);
			} catch (IOException i) {
			}
			Collections.sort(long_grain_list, new Comparator<aGrain>() {
				@Override
				public int compare(aGrain g1, aGrain g2) {
					if (g1.get_area() == g2.get_area()) {
						return (g1.get_seq() < g2.get_seq() ? 1 : -1);
					}
					return (g1.get_area() < g2.get_area() ? 1 : -1);
				}
			});
			try {
				PrintWriter dout_grain_list = new PrintWriter(user_dir + "_Grains_listing_0.txt");
				dout_grain_list.println("Seq_no, q value, row, col, area, perimeter, imp within grain, imp on boundary");
				for (aGrain gr : long_grain_list) {
					dout_grain_list.println(Integer.toString(gr.get_seq()) + "," + Short.toString(gr.get_q_val()) + "," + Short.toString(gr.get_row()) + "," + Short.toString(gr.get_col()) + "," + Long.toString(gr.get_area()) + "," + Long.toString(gr.get_perim()) + "," + Integer.toString(gr.get_imp_in_belly()) + "," + Integer.toString(gr.get_imp_total() - gr.get_imp_in_belly()));
				}
				dout_grain_list.close();
			} catch (IOException e) {
			}
			in_long_analysis = false;
		}

		private class find_long_area {

			private int unprocessed = 0;
			private int processed = 0;
			private boolean still_to_process = true;							//This flag controls the queue processing
			private long area = 0;
			private long perim = 0;
			private short curr_row;
			private short curr_col;
			private short ini_row;
			private short ini_col;
			private short q_val;
			private aGrain thisgrain;
			private int tot_imp;
			private int belly_imp;

			public find_long_area(aGrain the_grain) {
				q_val = the_grain.get_q_val();
				curr_row = (short) (the_grain.get_address() / BASE);
				curr_col = (short) (the_grain.get_address() % BASE);
				thisgrain = the_grain;
				ini_row = curr_row;
				ini_col = curr_col;
				return;
			}

			public void compute_long_area() {
				unprocessed = 0;
				processed = 0;
				still_to_process = true;							//This flag controls the queue processing
				area = 0L;
				perim = 0;

				int[] queue = new int[long_q_area[q_val - 1] + 1];
				boolean[] que_st = new boolean[long_q_area[q_val - 1] + 1];
				int[] queue_perim = new int[long_q_area[q_val - 1] + 1];		//This queue will store all perimeter element queue
				int[] impurity_queue = new int[impurity_count];

				queue[0] = BASE * curr_row + curr_col;							//Initialize the queue by storing the current starting address
				que_st[0] = false;
				dir_vectors dir = new dir_vectors();				//generate the array of control indices for computing immediate neighbourhood
				queue_perim[0] = BASE * curr_row + curr_col;
				perim = 1;

				do {

					//We take the starting cell of the grain, find all matching neighbours, and then for each neighbour so found,
					//we check if its already in the queue or not.
					//If not, then insert it in increasing order (keeps the queue array sorted, and increase the unprocessed variable (this
					//becomes eqvt to queue size).
					//We now proceed to locate all neighbours of the given input cell.
					boolean is_on_grain_edge = dir.set_val(curr_row, curr_col);		//we get the direction vectors from the current cell (range -1 to 1)

					for (short x = dir.get_st_val_i(); x <= dir.get_end_val_i(); x++) {	//we look at neighbouring cells for matching cells
						for (short y = dir.get_st_val_j(); y <= dir.get_end_val_j(); y++) {
							if ((x == 0) && (y == 0)) {
								continue;							//dont count yourself as your own neighbour, nor can oneself be an impurity
							}
							if (long_state_matrix[curr_row + x][curr_col + y] == IMM) {
								boolean found = false;
								int new_imp = (curr_row + x) * BASE + (curr_col + y);
								for (int z = 0; z < tot_imp; z++) {
									if (impurity_queue[z] == new_imp) {
										found = true;
									}
								}
								if (!(found)) {
									impurity_queue[tot_imp] = new_imp;
									tot_imp++;
								}
							} else {
								if (long_state_matrix[curr_row + x][curr_col + y] == q_val) {		//if there is a neighbouring cell matching our q_val
									int new_entry = (BASE * (curr_row + x)) + (curr_col + y);	//new entry into the queue,to be inserted in a sorted manner
									//the queue contains "unprocessed" no of elements
									boolean found = false;								//this flag tracks if this neighbour has already been put in queue
									int where = 0;										//this will point to where to insert the new_entry in the queue
									for (int z = 0; z < unprocessed; z++) {
										if (queue[z] == new_entry) {
											found = true;								//this one already exists in queue - so ignore this neighbour
										}
										if (queue[z] < new_entry) {
											where++;
										}
									}
									if (found) {
										continue;										//this neighbour has already been inserted into the array
									} else {
										//We push all elements from (where+1) till unprocessed by one place, and insert this new element in the gap
										for (int z = unprocessed; z > where; z--) {
											queue[z] = queue[z - 1];					//move the addresses of the neighbours in the queue
											que_st[z] = que_st[z - 1];					//move the flags representing the processing state also
										}
										if (where <= processed) {
											processed++;								//Processed points to the current location, so update that too
										}
										//System.out.println("Entering element "+new_entry+" at "+where);
										queue[where] = new_entry;						//Insert new entry made into the queue
										que_st[where] = false;							//Set new entry processing state as false-obviously not yet processed
										unprocessed++;									//Increase the size of the queue
									}
								}  //End of loop when a matching neighbour is found, and inserted into the queue
							}
						} //End of for loop
					} //End of for loops to test all neighbours.
	 /*
					 * The first part of the algorithm is over - we have added to the queue all such neighbours that are of same
					 * q_val as the given cell, ensuring they are inserted in a sorted manner, and are NOT duplicated.
					 *
					 * Now we commence the second part, where we process the current queue entry for area. We also negate the
					 * q_entry, so that its not double counted in the area computation.
					 */
					boolean is_found = false;
					for (int k = 0; k < perim; k++) {
						if (queue_perim[k] == (curr_row * BASE + curr_col)) {
							is_found = true;
						}
					}
					if (!(is_found)) {
						queue_perim[(int) (perim)] = curr_row * BASE + curr_col;
						perim++;
					}
					que_st[processed] = true;
					area++;							//current cell is accounted for.
					long_state_matrix[curr_row][curr_col] = (short) ((-1) * q_val);

					//Now we scan the whole queue to find the first "unprocessed element" and do this loop again. If no such element is left, then
					//this grain is over, we reset the still_to_process flag, and gracefully proceed to the computation of perimeter..
					boolean found_unproc = false;
					for (processed = 0; processed < unprocessed; processed++) {
						if (que_st[processed] == false) {
							found_unproc = true;
							break;
						}
					}
					if (found_unproc) {
						int addr_to_process = queue[processed];
						curr_row = (short) (addr_to_process / BASE);		//convert the address stored in queue back to row,col format
						curr_col = (short) (addr_to_process % BASE);
					} else {
						still_to_process = false;							//there are no unprocessed queue entries left, so exit the while loop
					}
				} while (still_to_process);

				/*
				 * Now we begin the second pass along the grain. We reset all grains status to false (this is just to reuse the
				 * memory, otherwise we would need another array of status flags corresponding to the perimeter queue) and then
				 * proceed to analyze the queue_perim sequence - this list contains unique addresses within the grains, that have at
				 * least ONE neighbour with a q_val not equal to theirs, excluding the guard rows/columns
				 */
				for (int z = 0; z < perim; z++) {
					curr_row = (short) (queue_perim[z] / BASE);
					curr_col = (short) (queue_perim[z] % BASE);
					if ((long_state_matrix[curr_row][curr_col + 1] == (-1) * q_val)
						&& (long_state_matrix[curr_row][curr_col - 1] == (-1) * q_val)
						&& (long_state_matrix[curr_row + 1][curr_col] == (-1) * q_val)
						&& (long_state_matrix[curr_row - 1][curr_col] == (-1) * q_val)
						&& (long_state_matrix[curr_row + 1][curr_col + 1] == (-1) * q_val)
						&& (long_state_matrix[curr_row + 1][curr_col - 1] == (-1) * q_val)
						&& (long_state_matrix[curr_row - 1][curr_col + 1] == (-1) * q_val)
						&& (long_state_matrix[curr_row - 1][curr_col - 1] == (-1) * q_val)) {
						perim--;
					}
				}
				for (int i = 0; i < tot_imp; i++) {
					curr_row = (short) (impurity_queue[i] / BASE);
					curr_col = (short) (impurity_queue[i] % BASE);
					if (((long_state_matrix[curr_row][curr_col + 1] == (-1) * q_val) || (long_state_matrix[curr_row][curr_col + 1] == IMM))
						&& ((long_state_matrix[curr_row][curr_col - 1] == (-1) * q_val) || (long_state_matrix[curr_row][curr_col - 1] == IMM))
						&& ((long_state_matrix[curr_row + 1][curr_col] == (-1) * q_val) || (long_state_matrix[curr_row + 1][curr_col] == IMM))
						&& ((long_state_matrix[curr_row - 1][curr_col] == (-1) * q_val) || (long_state_matrix[curr_row - 1][curr_col] == IMM))
						&& ((long_state_matrix[curr_row + 1][curr_col + 1] == (-1) * q_val) || (long_state_matrix[curr_row + 1][curr_col + 1] == IMM))
						&& ((long_state_matrix[curr_row + 1][curr_col - 1] == (-1) * q_val) || (long_state_matrix[curr_row + 1][curr_col - 1] == IMM))
						&& ((long_state_matrix[curr_row - 1][curr_col + 1] == (-1) * q_val) || (long_state_matrix[curr_row - 1][curr_col + 1] == IMM))
						&& ((long_state_matrix[curr_row - 1][curr_col - 1] == (-1) * q_val) || (long_state_matrix[curr_row - 1][curr_col - 1] == IMM))) {
						belly_imp++;
					}
				}
				thisgrain.add_area(area);
				thisgrain.add_perim(perim);
				thisgrain.add_imp_total(tot_imp);
				thisgrain.add_imp_in_belly(belly_imp);
				long_grain_list.add(thisgrain);
				return;
			} //End of method call
		}//End of the private class
	} //End of Runnable long_area_analysis

	public static class display_image implements Runnable {

		private int[] q_freq = new int[max_q];
		private int[][] max_5 = new int[2][5];					//Allocate an array of the max 5 values
		public BufferedImage crystal_image;
		private ImageIcon crys_copy;
		private scrollable_image crystal_scroll_image;
		public BufferedImage legend_image;
		private ImageIcon legend_copy;
		private scrollable_legend legend_scroll_image;
		public BufferedImage right_legend_image;
		private ImageIcon right_legend_copy;
		private right_scrollable_legend right_legend_scroll_image;
		private NumberFormat fmt;
		private NumberFormat fmt_double;
		private long time_at_last_click;

		public display_image() {
			return;
		}

		@Override
		public void run() {
			try {
				image_frame display_frame = new image_frame();			//Creates the extended JFrame
				display_frame.setVisible(true);							//Sets the JFrame to be visible

				do {
					display_frame.repaint();						//Repaints it frequently
					Thread.sleep(1000);								//Go to sleep, so that the CPU is not blocked only by display
					for (short i = 0; i < max_q; i++) {				//Build the frequency chart of the q_values distribution
						q_freq[i] = 0;
					}
					for (short i = 1; i < ARR_LIM; i++) {
						for (short j = 1; j < ARR_LIM; j++) {
							short q_val = state_matrix[i][j];
							if (q_val == IMM) {
								continue;
							}
							if (q_val < 0) {						//because this thread may read state_matrix in middle of an area
								q_val = (short) ((-1) * (q_val));		//compute, it can very well have a negative value.
							}
							q_freq[q_val - 1]++;
						}
					}
					//Now we process this q_area array to find the five most frequent q _values
					for (short k = 0; k < 5; k++) {
						int temp_max = 0;
						int temp_max_q_val = 0;
						for (int i = 0; i < max_q; i++) {
							if ((q_freq[i] >= temp_max) && (i != temp_max_q_val - 1)) {
								temp_max = q_freq[i];
								temp_max_q_val = i + 1;	//as q_vals range from 1 to max_q
							}
						}
						max_5[0][k] = temp_max_q_val;
						max_5[1][k] = temp_max;
						q_freq[temp_max_q_val - 1] = 0;	//So that next iteration finds the next most max value, restored when done
					}
					for (short k = 0; k < 5; k++) {
						q_freq[max_5[0][k] - 1] = max_5[1][k];
					}
				} while (true);
			} catch (InterruptedException e) {
				//We should close the JFrame here
			}
		}

		private class image_frame extends JFrame {			//Builds the basic frame for display

			private final int FRAME_DIMN_X = 1400;
			private final int FRAME_DIMN_Y = 825;
			private final int TOP_PANEL_X = 0;
			private final int TOP_PANEL_Y = 0;
			private final int TOP_PANEL_DIMN_X = 1400;
			private final int TOP_PANEL_DIMN_Y = 65;
			private final int TOP_MOUSE_PANEL_X = 0;
			private final int TOP_MOUSE_PANEL_Y = 55;
			private final int TOP_MOUSE_PANEL_DIMN_X = 1400;
			private final int TOP_MOUSE_PANEL_DIMN_Y = 25;
			private final int CENTRE_IMAGE_X = 180;
			private final int CENTRE_IMAGE_Y = 80;			//cannot be less than TOP_PANEL_DIMN_Y
			private final int CENTRE_IMAGE_DIMN_X = 840;
			private final int CENTRE_IMAGE_DIMN_Y = 700;
			private final int LEFT_INFO_PANEL_X = 0;
			private final int LEFT_INFO_PANEL_Y = 80;		//has to be same as TOP_PANEL_DIMN_Y
			private final int LEFT_INFO_PANEL_DIMN_X = 180;	//has to be same as CENTRE_IMAGE_X
			private final int LEFT_INFO_PANEL_DIMN_Y = 220;
			private final int LEFT_LEGEND_PANEL_X = 0;
			private final int LEFT_LEGEND_PANEL_Y = 300;		//has to be same as TOP_PANEL_DIMN_Y
			private final int LEFT_LEGEND_PANEL_DIMN_X = 180;	//has to be same as CENTRE_IMAGE_X
			private final int LEFT_LEGEND_PANEL_DIMN_Y = 480;
			private final int RIGHT_LEGEND_PANEL_X = 1020;
			private final int RIGHT_LEGEND_PANEL_Y = 80;		//has to be same as TOP_PANEL_DIMN_Y
			private final int RIGHT_LEGEND_PANEL_DIMN_X = 360;	//has to be same as CENTRE_IMAGE_X
			private final int RIGHT_LEGEND_PANEL_DIMN_Y = 700;

			public image_frame() {
				this.setLocationByPlatform(true);
				fmt = new DecimalFormat("###,###,###,###");
				fmt_double = new DecimalFormat("###,###,###,##0.000");
				this.setTitle("Grain Image of " + fmt.format(state_size) + "x" + fmt.format(state_size) + " with q-value " + max_q + " initial Hamiltonian: " + fmt.format(ini_hamil) + " and " + fmt.format(impurity_count) + " impurities");
				this.setAlwaysOnTop(true);
				this.setMinimumSize(new Dimension(FRAME_DIMN_X, FRAME_DIMN_Y));
				this.setResizable(false);
				this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

				JLayeredPane layered_pane = new JLayeredPane();
				layered_pane.setPreferredSize(new Dimension(FRAME_DIMN_X, FRAME_DIMN_Y));

				top_info_panel top_data = new top_info_panel();			//Creates a Component type which has all data sets
				top_data.setBounds(TOP_PANEL_X, TOP_PANEL_Y, TOP_PANEL_DIMN_X, TOP_PANEL_DIMN_Y);
				layered_pane.add(top_data, new Integer(0));				//Add this to the layered pane

				top_mouse_info_panel top_mouse_data = new top_mouse_info_panel();			//Creates a Component type which has all data sets
				top_mouse_data.setBounds(TOP_MOUSE_PANEL_X, TOP_MOUSE_PANEL_Y, TOP_MOUSE_PANEL_DIMN_X, TOP_MOUSE_PANEL_DIMN_Y);
				layered_pane.add(top_mouse_data, new Integer(1));				//Add this to the layered pane

				JComponent scroll_crys_image = new scroll_image();
				scroll_crys_image.setBounds(CENTRE_IMAGE_X, CENTRE_IMAGE_Y, CENTRE_IMAGE_DIMN_X, CENTRE_IMAGE_DIMN_Y);
				layered_pane.add(scroll_crys_image, new Integer(2));

				left_info_panel left_dat_panel = new left_info_panel();
				left_dat_panel.setBounds(LEFT_INFO_PANEL_X, LEFT_INFO_PANEL_Y, LEFT_INFO_PANEL_DIMN_X, LEFT_INFO_PANEL_DIMN_Y);
				layered_pane.add(left_dat_panel, new Integer(3));				//Add this to the layered pane

				JComponent scroll_left_legend = new scroll_left_legend();
				scroll_left_legend.setBounds(LEFT_LEGEND_PANEL_X, LEFT_LEGEND_PANEL_Y, LEFT_LEGEND_PANEL_DIMN_X, LEFT_LEGEND_PANEL_DIMN_Y);
				layered_pane.add(scroll_left_legend, new Integer(4));

				JComponent scroll_right_legend = new scroll_right_legend();
				scroll_right_legend.setBounds(RIGHT_LEGEND_PANEL_X, RIGHT_LEGEND_PANEL_Y, RIGHT_LEGEND_PANEL_DIMN_X, RIGHT_LEGEND_PANEL_DIMN_Y);
				layered_pane.add(scroll_right_legend, new Integer(5));

				add(layered_pane);
			}
		} //End of image frame

		private class top_info_panel extends JComponent {

			@Override
			public void paintComponent(Graphics top) {
				/*
				 * First we draw the top panel part.
				 */
				Font sans_bold = new Font("SansSerif", Font.BOLD, 12);
				Font sans_normal = new Font("SansSerif", Font.PLAIN, 12);
				top.setFont(sans_bold);
				top.setColor(Color.BLUE);
				top.drawString("This program has been written by Gautam Mukherjee, Piyali Mukherjee, and Aniruddh Bhat and is property of Prof. K R Phaneesh, Assoc. Prof., MSRIT, Bangalore (phaneeshkr@msrit.edu)", 20, 15);
				top.drawString("MCS no: ", 20, 30);
				top.drawString("Count of Exchanges: ", 20, 45);
				if (prop_for_T > 0.0) {
					top.drawString("Thermal flips: ", 270, 45);
				}
				top.drawString("Running time: ", 270, 30);
				if (in_long_analysis) {
					top.setFont(sans_normal);
					top.drawString("Initial matrix analysis: " + fmt_double.format(percent_ini_file_analysed) + "% done", 20, 60);
				}
				if ((first_file_save_cntr) && (!(in_saving_stats))) {
					top.setColor(Color.red);
					top.setFont(sans_bold);
					top.drawString("Last snapshot: ", 500, 30);
					top.drawString(" saved at: ", 625, 30);
					top.drawString("after MCS: ", 795, 30);
					top.drawString("Hamil: ", 925, 30);
					top.drawString("Count of exchanges: ", 1085, 30);//895
					top.drawString("No of grains: ", 500, 45);
					top.drawString("with avg area: ", 675, 45);
					if (prop_for_T > 0.0) {
						top.drawString("Thermal flips: ", 1085, 45);
					}
					top.drawString("Total Iterations :", 925, 45);
				} else {
					top.setFont(sans_normal);
					top.drawString("Please wait till the first stat data is computed and saved after " + (min_ini_mcs_to_wait) + " MCS steps", 500, 30);
					top.drawString("If set_tracker is set, then the first few MCS will take long time (sometimes very long time) and then steadily accelerate", 500, 45);
				}

				top.setFont(sans_normal);
				top.setColor(Color.BLUE);
				top.drawString(fmt.format(mcs_no) + " of " + fmt.format(no_of_mcs_steps), 70, 30);
				top.drawString(fmt.format(flip_counter), 140, 45); //flip_counter
				if (prop_for_T != 0.0) {
					top.drawString(fmt.format(thermal_flips), 350, 45); //thermal_flips
				}
				top.drawString(fmt.format(((System.currentTimeMillis() - run_start_time) / (1000))) + " secs", 350, 30);
				if ((first_file_save_cntr) && (!(in_saving_stats))) {
					top.setColor(Color.red);
					top.drawString(fmt.format(file_save_cntr), 585, 30);		//Integer.toString(file_save_cntr)
					top.drawString(fmt.format((time_at_last_save - run_start_time) / (1000)) + " secs", 685, 30);//((time_at_last_save - run_start_time) / (1000))
					top.drawString(fmt.format(iter_at_last_save), 855, 30);//
					top.drawString(fmt.format(hamil_at_last_save), 975, 30);	//hamil_at_last_save
					top.drawString(fmt.format(exchgs_at_last_save), 1210, 30); //1015
					if (prop_for_T > 0.0) {
						top.drawString(fmt.format(thermal_exchgs_at_last_save), 1165, 45);
					}
					top.drawString(fmt.format(total_grains_at_last_save), 575, 45);
					top.drawString(fmt_double.format(avg_area_at_last_save), 765, 45);
					top.drawString(fmt.format(prev_no_of_mcs + iter_at_last_save), 1020, 45); //prev_no_of_mcs + iter_at_last_save
				}
				crystal_image = draw_crystal_image();
				crys_copy = new ImageIcon(crystal_image);
				crystal_scroll_image.setIcon(crys_copy);

				legend_image = draw_legend_image();
				legend_copy = new ImageIcon(legend_image);
				legend_scroll_image.setIcon(legend_copy);

				right_legend_image = draw_table_image();
				right_legend_copy = new ImageIcon(right_legend_image);
				right_legend_scroll_image.setIcon(right_legend_copy);

			}
		}

		private class top_mouse_info_panel extends JComponent {

			@Override
			public void paintComponent(Graphics top_mouse) {
				if (click_set) {
					long time_now = System.currentTimeMillis();
					if (first_file_save_cntr) {
						Font sans_bold = new Font("SansSerif", Font.BOLD, 12);
						top_mouse.setFont(sans_bold);
						top_mouse.setColor(Color.RED);
						top_mouse.drawString("Mouse clicked on X: " + fmt.format(mouse_y) + " Y: " + fmt.format(mouse_x), 500, 12);

						if (click_processed) {
							Color shade = new Color(colours[click_q_val]);
							top_mouse.setColor(shade);
							top_mouse.fillRoundRect(700, 0, 40, 20, 10, 10);
							top_mouse.setColor(Color.RED);
							top_mouse.drawString(" q val: " + click_q_val + "  area: " + fmt.format(click_area) + "  perim: " + fmt.format(click_perim) + "  total imp: " + fmt.format(click_total_imp) + "  imp within in grain: " + fmt.format(click_imp_in_belly), 750, 12);
							if ((click_set) && ((time_now - when_click_processed) > 10000)) {
								mouse_x = 0;
								mouse_y = 0;
								click_set = false;
								click_processed = false;
							}
						} else {
							top_mouse.drawString("Processing this grain ... please wait ...", 700, 12);
						}
					} else {
						Font sans_normal = new Font("SansSerif", Font.PLAIN, 12);
						top_mouse.setColor(Color.RED);
						top_mouse.setFont(sans_normal);
						top_mouse.drawString("Mouse clicked on X: " + fmt.format(mouse_x) + " Y: " + fmt.format(mouse_y) + " - please wait for first file to be saved", 500, 10);
						if ((time_now - time_at_last_click) > 5000) {
							mouse_x = 0;
							mouse_y = 0;
							click_set = false;
							click_processed = false;
						}
					}
				}
				Font sans_real_bold = new Font("SansSerif", Font.BOLD, 24);
				top_mouse.setColor(Color.RED);
				top_mouse.setFont(sans_real_bold);
				top_mouse.drawString("Y", 240, 22);
				top_mouse.fillRect(260, 10, 3, 3);
				top_mouse.fillRect(260, 16, 3, 3);
				top_mouse.fillRect(265, 12, 8, 4);
				int[] x_pts = new int[3];
				int[] y_pts = new int[3];
				x_pts[0] = 273;
				y_pts[0] = 8;
				x_pts[1] = 273;
				y_pts[1] = 20;
				x_pts[2] = 285;
				y_pts[2] = 14;
				top_mouse.fillPolygon(x_pts, y_pts, 3);
			}
		}

		private BufferedImage draw_crystal_image() {
			BufferedImage local_image = new BufferedImage(state_size + 1, state_size + 1, BufferedImage.TYPE_INT_ARGB);
			WritableRaster raster = local_image.getRaster();
			ColorModel model = local_image.getColorModel();

			for (int i = 1; i < ARR_LIM; i++) {
				for (int j = 1; j < ARR_LIM; j++) {
					short q_val = state_matrix[i][j];
					if (q_val < 0) {
						q_val = (short) ((-1) * q_val);
					}
					Color shade = new Color(colours[q_val]);
					Object exact_shade = model.getDataElements(shade.getRGB(), null);	//convert the colour into Object form
					raster.setDataElements(j - 1, i - 1, exact_shade);				//set the pixel into the exact shade
				}
			}
			return (local_image);
		}//End of draw_crystal_image

		private class center_info_panel extends JComponent {

			private BufferedImage image;

			public BufferedImage get_image() {
				image = draw_crystal_image();
				return (image);
			}

			private BufferedImage draw_crystal_image() {
				BufferedImage local_image = new BufferedImage(state_size + 1, state_size + 1, BufferedImage.TYPE_INT_ARGB);
				WritableRaster raster = local_image.getRaster();
				ColorModel model = local_image.getColorModel();

				for (int i = 1; i < ARR_LIM; i++) {
					for (int j = 1; j < ARR_LIM; j++) {
						short q_val = state_matrix[i][j];
						if (q_val < 0) {
							q_val = (short) ((-1) * q_val);
						}
						Color shade = new Color(colours[q_val]);
						Object exact_shade = model.getDataElements(shade.getRGB(), null);	//convert the colour into Object form
						raster.setDataElements(i - 1, j - 1, exact_shade);						//set the pixel into the exact shade
					}
				}
				return (local_image);
			}//End of draw_crystal_image
		} //End of JComponent center_info_panel

		private class left_info_panel extends JComponent {

			@Override
			public void paintComponent(Graphics left) {
				/*
				 * First we draw the top sub_panel part.
				 */
				Graphics2D left_gphx = (Graphics2D) (left);
				Font sans_bold = new Font("SansSerif", Font.BOLD, 12);
				Font sans_normal = new Font("SansSerif", Font.PLAIN, 12);

				left.setFont(sans_bold);
				left.setColor(Color.BLUE);
				int loc_x = 15;
				int loc_y = 10;
				left.drawString("5 most frequent q_vals", loc_x, loc_y);
				left.setFont(sans_normal);
				left.drawString("Q val", loc_x + 15, loc_y + 15);
				left.drawString("Frequency", 85, loc_y + 15);
				loc_y = 60;
				for (short i = 0; i < 5; i++) {
					RoundRectangle2D rect = new RoundRectangle2D.Float(15.0F, (float) (loc_y + (i - 1) * 30), 40.0F, 20.0F, 10.0F, 10.0F);
					Color shade = new Color(colours[max_5[0][i]]);
					left_gphx.setColor(shade);
					left_gphx.fill(rect);
					left_gphx.drawString(Integer.toString(max_5[0][i]), 60, (int) (loc_y + 15 + (i - 1) * 30));
					left_gphx.drawString(fmt.format(max_5[1][i]), 85, (int) (loc_y + 15 + (i - 1) * 30));
				}
				left.setFont(sans_bold);
				left.setColor(Color.BLUE);
				left.drawLine(0, 180, 180, 180);
				left.drawString("Legend", loc_x, 200);
				left.setFont(sans_normal);
				left.drawString("Q val", loc_x + 15, 215);
				left.drawString("Frequency", 85, 215);
				/*
				 * Technically, not a part of the panel, but we draw it here to keep it in scroll screen
				 */
				Font sans_real_bold = new Font("SansSerif", Font.BOLD, 24);
				left.setColor(Color.RED);
				left.setFont(sans_real_bold);
				left.drawString("X", 160, 70);
				left.fillRect(163, 75, 3, 3);
				left.fillRect(169, 75, 3, 3);
				left.fillRect(166, 80, 4, 8);
				int[] x_pts = new int[3];
				int[] y_pts = new int[3];
				x_pts[0] = 163;
				y_pts[0] = 88;
				x_pts[1] = 173;
				y_pts[1] = 88;
				x_pts[2] = 168;
				y_pts[2] = 100;
				left.fillPolygon(x_pts, y_pts, 3);
			}
		} //End of class left_info_panel

		public class scroll_image extends JComponent {

			private Rule col_view;
			private Rule row_view;
			//private JToggleButton isMetric;

			public scroll_image() {
				setLayout(new BoxLayout(this, BoxLayout.LINE_AXIS));

				//Create the row and column headers.
				col_view = new Rule(Rule.HORIZONTAL, true);
				row_view = new Rule(Rule.VERTICAL, true);
				col_view.setPreferredWidth(state_size);
				row_view.setPreferredHeight(state_size);

				//Set up the scroll pane.
				center_info_panel crys_image = new center_info_panel();
				crystal_image = crys_image.get_image();					//Store this image
				crys_copy = new ImageIcon(crystal_image);
				crystal_scroll_image = new scrollable_image(crys_copy, col_view.getIncrement());
				crystal_scroll_image.addMouseListener(new mouse_click());
				JScrollPane image_scroll_pane = new JScrollPane(crystal_scroll_image);
				image_scroll_pane.setPreferredSize(new Dimension(state_size, state_size));
				image_scroll_pane.setViewportBorder(BorderFactory.createLineBorder(Color.black));
				image_scroll_pane.setColumnHeaderView(col_view);
				image_scroll_pane.setRowHeaderView(row_view);

				//Set the corners.
				image_scroll_pane.setCorner(JScrollPane.UPPER_LEFT_CORNER, new corner());
				image_scroll_pane.setCorner(JScrollPane.LOWER_LEFT_CORNER, new corner());
				image_scroll_pane.setCorner(JScrollPane.UPPER_RIGHT_CORNER, new corner());
				image_scroll_pane.setCorner(JScrollPane.LOWER_RIGHT_CORNER, new corner());
//image_scroll_pane.addMouseListener(new mouse_click());
				//Put it in this panel.
				add(image_scroll_pane);
			}
		}

		private class mouse_click extends MouseAdapter {

			@Override
			public void mouseClicked(MouseEvent event) {
				Point2D point = event.getPoint();
				if (!click_set) {
					mouse_x = (short) (point.getX());
					mouse_y = (short) (point.getY());
					time_at_last_click = System.currentTimeMillis();
					click_set = true;
				} //Only of currently no click is remaining unprocessed.
			}
		}

		public class Rule extends JComponent {

			public static final int HORIZONTAL = 0;
			public static final int VERTICAL = 1;
			public static final int SIZE = 15;
			public int orientation;
			private int increment;
			private int units;

			public Rule(int o, boolean m) {
				orientation = o;
				setIncrementAndUnits();
			}

			private void setIncrementAndUnits() {
				units = 100;
				increment = units / 2;
			}

			public int getIncrement() {
				return increment;
			}

			public void setPreferredHeight(int ph) {
				setPreferredSize(new Dimension(SIZE, ph));
			}

			public void setPreferredWidth(int pw) {
				setPreferredSize(new Dimension(pw, SIZE));
			}

			@Override
			protected void paintComponent(Graphics g) {
				/*
				 * Next we draw the revised scales as the scrollbars would have moved
				 */
				Rectangle drawHere = g.getClipBounds();

				// Fill clipping area with light blue.
				g.setColor(new Color(185, 225, 240));
				g.fillRect(drawHere.x, drawHere.y, drawHere.width, drawHere.height);

				// Do the ruler labels in a small font that's black.
				g.setFont(new Font("SansSerif", Font.PLAIN, 10));
				g.setColor(Color.BLUE);

				// Some vars we need.
				int end = 0;
				int start = 0;
				int tickLength = 0;
				String text = null;

				// Use clipping bounds to calculate first and last tick locations.
				if (orientation == HORIZONTAL) {
					start = (drawHere.x / increment) * increment;
					end = (((drawHere.x + drawHere.width) / increment) + 1) * increment;
				} else {
					start = (drawHere.y / increment) * increment;
					end = (((drawHere.y + drawHere.height) / increment) + 1) * increment;
				}

				// Make a special case of 0 to display the number
				// within the rule and draw a units label.
				if (start == 0) {
					tickLength = 5;
					//g.setFont(new Font("SansSerif", Font.BOLD, 16));
					if (orientation == HORIZONTAL) {
						g.drawLine(0, SIZE - 1, 0, SIZE - tickLength - 1);
						g.drawString("0", 5, 11);
					} else {
						g.drawLine(SIZE - 1, 0, SIZE - tickLength - 1, 0);
						g.drawString("0", 2, 15);
					}
					g.setFont(new Font("SansSerif", Font.PLAIN, 10));
					text = null;
					start = increment;
				}

				// ticks and labels
				for (int i = start; i < end; i += increment) {
					if (i % units == 0) {
						tickLength = 10;
						text = Integer.toString(i / units);
					} else {
						tickLength = 7;
						text = null;
					}

					if (orientation == HORIZONTAL) {
						g.drawLine(i, SIZE - 1, i, SIZE - tickLength - 1);
						if (text != null) {
							if (i < start + 10) {
								g.drawString(text, i - 7, 11);
							} else {
								g.drawString(text, i - 12, 11);
							}
						}
					} else {
						g.drawLine(SIZE - 1, i, SIZE - tickLength - 1, i);
						if (text != null) {
							if (i < start + 10) {
								g.drawString(text, 9, i - 1);
							} else {
								g.drawString(text, 2, i - 1);
							}
						}
					}

				}
			}
		} //End of the Rule class

		public class corner extends JComponent {

			@Override
			protected void paintComponent(Graphics g) {
				g.setColor(new Color(255, 255, 255));
				g.fillRect(0, 0, getWidth(), getHeight());
			}
		} //End of the Corner class

		public class scrollable_image extends JLabel implements Scrollable, MouseMotionListener {

			private int maxUnitIncrement = 1;

			public scrollable_image(ImageIcon i, int m) {
				super(i);
				maxUnitIncrement = m;

				//Let the user scroll by dragging to outside the window.
				setAutoscrolls(true); //enable synthetic drag events
				addMouseMotionListener(this); //handle mouse drags
			}
			//Methods required by the MouseMotionListener interface:

			@Override
			public void mouseMoved(MouseEvent e) {
			}

			@Override
			public void mouseDragged(MouseEvent e) {
				//The user is dragging us, so scroll!
				Rectangle r = new Rectangle(e.getX(), e.getY(), 1, 1);
				scrollRectToVisible(r);
			}

			@Override
			public Dimension getPreferredSize() {

				return super.getPreferredSize();
			}

			@Override
			public Dimension getPreferredScrollableViewportSize() {
				return getPreferredSize();
			}

			@Override
			public int getScrollableUnitIncrement(Rectangle visibleRect, int orientation, int direction) {
				//Get the current position.
				int currentPosition = 0;
				if (orientation == SwingConstants.HORIZONTAL) {
					currentPosition = visibleRect.x;
				} else {
					currentPosition = visibleRect.y;
				}

				//Return the number of pixels between currentPosition
				//and the nearest tick mark in the indicated direction.
				if (direction < 0) {
					int newPosition = currentPosition - (currentPosition / maxUnitIncrement) * maxUnitIncrement;
					return (newPosition == 0) ? maxUnitIncrement : newPosition;
				} else {
					return ((currentPosition / maxUnitIncrement) + 1) * maxUnitIncrement - currentPosition;
				}
			}

			@Override
			public int getScrollableBlockIncrement(Rectangle visibleRect, int orientation, int direction) {
				if (orientation == SwingConstants.HORIZONTAL) {
					return visibleRect.width - maxUnitIncrement;
				} else {
					return visibleRect.height - maxUnitIncrement;
				}
			}

			@Override
			public boolean getScrollableTracksViewportWidth() {
				return false;
			}

			@Override
			public boolean getScrollableTracksViewportHeight() {
				return false;
			}

			public void setMaxUnitIncrement(int pixels) {
				maxUnitIncrement = pixels;
			}
		}

		private BufferedImage draw_legend_image() {
			BufferedImage local_image = new BufferedImage(200, 30 * (max_q + 1), BufferedImage.TYPE_INT_ARGB);
			Graphics2D left_gphx = local_image.createGraphics();
			Font sans_normal = new Font("SansSerif", Font.PLAIN, 12);
			left_gphx.setColor(Color.BLUE);
			left_gphx.setFont(sans_normal);
			int loc_y = 15;
			for (short i = 1; i <= max_q; i++) {
				RoundRectangle2D rect = new RoundRectangle2D.Float(15.0F, (float) (loc_y + (i - 1) * 30), 40.0F, 20.0F, 10.0F, 10.0F);
				Color shade = new Color(colours[i]);
				left_gphx.setColor(shade);
				left_gphx.fill(rect);
				left_gphx.setColor(Color.BLUE);
				left_gphx.drawString(Short.toString(i), 60, (int) (loc_y + 15 + (i - 1) * 30));
				left_gphx.drawString(fmt.format(q_freq[i - 1]), 85, (int) (loc_y + 15 + (i - 1) * 30));
			}
			return (local_image);
		}

		public class scroll_left_legend extends JComponent {

			public scroll_left_legend() {
				setLayout(new BoxLayout(this, BoxLayout.LINE_AXIS));

				//Set up the scroll pane.
				legend_image = draw_legend_image();					//Store this image
				legend_copy = new ImageIcon(legend_image);
				legend_scroll_image = new scrollable_legend(legend_copy, 1);
				JScrollPane legend_scroll_pane = new JScrollPane(legend_scroll_image); //,ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER);
				legend_scroll_pane.setPreferredSize(new Dimension(state_size, state_size));
				legend_scroll_pane.setCorner(JScrollPane.UPPER_RIGHT_CORNER, new corner());

				//Put it in this panel.
				add(legend_scroll_pane);
			}
		}

		public class scrollable_legend extends JLabel implements Scrollable, MouseMotionListener {

			private int maxUnitIncrement = 1;

			public scrollable_legend(ImageIcon i, int m) {
				super(i);
				maxUnitIncrement = m;

				//Let the user scroll by dragging to outside the window.
				setAutoscrolls(true); //enable synthetic drag events
				addMouseMotionListener(this); //handle mouse drags
			}
			//Methods required by the MouseMotionListener interface:

			@Override
			public void mouseMoved(MouseEvent e) {
			}

			@Override
			public void mouseDragged(MouseEvent e) {
				//The user is dragging us, so scroll!
				Rectangle r = new Rectangle(e.getX(), e.getY(), 1, 1);
				scrollRectToVisible(r);
			}

			@Override
			public Dimension getPreferredSize() {

				return super.getPreferredSize();
			}

			@Override
			public Dimension getPreferredScrollableViewportSize() {
				return getPreferredSize();
			}

			@Override
			public int getScrollableUnitIncrement(Rectangle visibleRect, int orientation, int direction) {
				//Get the current position.
				int currentPosition = 0;
				if (orientation == SwingConstants.HORIZONTAL) {
					currentPosition = visibleRect.x;
				} else {
					currentPosition = visibleRect.y;
				}

				//Return the number of pixels between currentPosition
				//and the nearest tick mark in the indicated direction.
				if (direction < 0) {
					int newPosition = currentPosition - (currentPosition / maxUnitIncrement) * maxUnitIncrement;
					return (newPosition == 0) ? maxUnitIncrement : newPosition;
				} else {
					return ((currentPosition / maxUnitIncrement) + 1) * maxUnitIncrement - currentPosition;
				}
			}

			@Override
			public int getScrollableBlockIncrement(Rectangle visibleRect, int orientation, int direction) {
				if (orientation == SwingConstants.HORIZONTAL) {
					return visibleRect.width - maxUnitIncrement;
				} else {
					return visibleRect.height - maxUnitIncrement;
				}
			}

			@Override
			public boolean getScrollableTracksViewportWidth() {
				return false;
			}

			@Override
			public boolean getScrollableTracksViewportHeight() {
				return false;
			}

			public void setMaxUnitIncrement(int pixels) {
				maxUnitIncrement = pixels;
			}
		} //End of class Scrollable legend

		private BufferedImage draw_table_image() {
			BufferedImage local_image = new BufferedImage(450, 30 * (MAX_DISPLAY + 1), BufferedImage.TYPE_INT_ARGB);
			Graphics2D rt_gphx = local_image.createGraphics();
			Font sans_normal = new Font("SansSerif", Font.PLAIN, 12);
			Font sans_bold = new Font("SansSerif", Font.BOLD, 12);
			rt_gphx.setColor(Color.BLUE);
			rt_gphx.setFont(sans_bold);
			rt_gphx.drawString("Top " + MAX_DISPLAY + " grain data", 130, 15);
			if ((first_file_save_cntr) && (!(in_saving_stats))) {
				int loc_y = 50;
				rt_gphx.setFont(sans_normal);
				rt_gphx.drawString("Q Val", 40, 30);
				rt_gphx.drawString("X", 90, 30);
				rt_gphx.drawString("Y", 130, 30);
				rt_gphx.drawString("Area", 170, 30);
				rt_gphx.drawString("Perimeter", 240, 30);
				rt_gphx.drawString("Tot Imp", 315, 30);
				rt_gphx.drawString("Imp in Belly", 380, 30);
				for (short i = 1; i <= MAX_DISPLAY; i++) {
					RoundRectangle2D rect = new RoundRectangle2D.Float(15.0F, (float) (loc_y), 40.0F, 20.0F, 10.0F, 10.0F);
					Color shade = new Color(colours[(short) (big_grains_list_at_last_save[0][i - 1])]);
					rt_gphx.setColor(shade);
					rt_gphx.fill(rect);
					rt_gphx.setColor(Color.BLUE);
					rt_gphx.drawString(Short.toString((short) (big_grains_list_at_last_save[0][i - 1])), 60, loc_y + 15);
					rt_gphx.drawString(fmt.format(big_grains_list_at_last_save[1][i - 1]), 90, loc_y + 15);
					rt_gphx.drawString(fmt.format(big_grains_list_at_last_save[2][i - 1]), 130, loc_y + 15);
					rt_gphx.drawString(fmt.format(big_grains_list_at_last_save[3][i - 1]), 170, loc_y + 15);
					rt_gphx.drawString(fmt.format(big_grains_list_at_last_save[4][i - 1]), 240, loc_y + 15);
					rt_gphx.drawString(fmt.format(big_grains_list_at_last_save[5][i - 1]), 315, loc_y + 15);
					rt_gphx.drawString(fmt.format(big_grains_list_at_last_save[6][i - 1]), 380, loc_y + 15);
					loc_y += 30;
				}
			} else {
				rt_gphx.setFont(sans_normal);
				rt_gphx.drawString("Please wait till the next stat data is computed and saved", 20, 30);
			}
			return (local_image);
		}

		public class scroll_right_legend extends JComponent {

			public scroll_right_legend() {
				setLayout(new BoxLayout(this, BoxLayout.LINE_AXIS));

				//Set up the scroll pane.
				right_legend_image = draw_table_image();					//Store this image
				right_legend_copy = new ImageIcon(right_legend_image);
				right_legend_scroll_image = new right_scrollable_legend(right_legend_copy, 1);
				JScrollPane right_legend_scroll_pane = new JScrollPane(right_legend_scroll_image); //,ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER);
				right_legend_scroll_pane.setPreferredSize(new Dimension(300, state_size));
				right_legend_scroll_pane.setCorner(JScrollPane.UPPER_RIGHT_CORNER, new corner());
				//Put it in this panel.
				add(right_legend_scroll_pane);
			}
		}

		public class right_scrollable_legend extends JLabel implements Scrollable, MouseMotionListener {

			private int maxUnitIncrement = 1;

			public right_scrollable_legend(ImageIcon i, int m) {
				super(i);
				maxUnitIncrement = m;

				//Let the user scroll by dragging to outside the window.
				setAutoscrolls(true); //enable synthetic drag events
				addMouseMotionListener(this); //handle mouse drags
			}
			//Methods required by the MouseMotionListener interface:

			@Override
			public void mouseMoved(MouseEvent e) {
			}

			@Override
			public void mouseDragged(MouseEvent e) {
				//The user is dragging us, so scroll!
				Rectangle r = new Rectangle(e.getX(), e.getY(), 1, 1);
				scrollRectToVisible(r);
			}

			@Override
			public Dimension getPreferredSize() {

				return super.getPreferredSize();
			}

			@Override
			public Dimension getPreferredScrollableViewportSize() {
				return getPreferredSize();
			}

			@Override
			public int getScrollableUnitIncrement(Rectangle visibleRect, int orientation, int direction) {
				//Get the current position.
				int currentPosition = 0;
				if (orientation == SwingConstants.HORIZONTAL) {
					currentPosition = visibleRect.x;
				} else {
					currentPosition = visibleRect.y;
				}

				//Return the number of pixels between currentPosition
				//and the nearest tick mark in the indicated direction.
				if (direction < 0) {
					int newPosition = currentPosition - (currentPosition / maxUnitIncrement) * maxUnitIncrement;
					return (newPosition == 0) ? maxUnitIncrement : newPosition;
				} else {
					return ((currentPosition / maxUnitIncrement) + 1) * maxUnitIncrement - currentPosition;
				}
			}

			@Override
			public int getScrollableBlockIncrement(Rectangle visibleRect, int orientation, int direction) {
				if (orientation == SwingConstants.HORIZONTAL) {
					return visibleRect.width - maxUnitIncrement;
				} else {
					return visibleRect.height - maxUnitIncrement;
				}
			}

			@Override
			public boolean getScrollableTracksViewportWidth() {
				return false;
			}

			@Override
			public boolean getScrollableTracksViewportHeight() {
				return false;
			}

			public void setMaxUnitIncrement(int pixels) {
				maxUnitIncrement = pixels;
			}
		} //End of class Scrollable legend
	} //End of Runnable display_image class
} //End of class Final_2D
