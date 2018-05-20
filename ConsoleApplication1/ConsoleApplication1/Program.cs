using System;
using System.IO;
using System.Diagnostics;
using Microsoft.Z3;
using System.Collections.Generic;

/**
 * - k = 0 (Multiple steps is not considered for vulnearability exploitation)
 * - Services are not considered to define traffic flows
 * 
 * Efficient by removing constant terms with constants
 * Removing Integer terms for isolation, diversity, resiliency, and usability
 */
class ConfigSynth
{
    Context z3;
    Solver slvr;

    static TextWriter twOut, twData;    // Output file

    //const String TIME_OUT = "12000000";   // How long we want to search for the model?  
    const String TIME_OUT = "1800000";
    const String TIME_OUT_SHORT = "1800000";   // How long we want to search for the model? This is for the improvement...
                                               //dd
    const int MAX_NUM_SOLUTION = 1;

    #region Constants
    const int NUM_OF_HOST = 20;
    const int NUM_OF_ROUTER = 8;
    const int NUM_OF_LINK = 28;

    const int TRANSITIVITY_LEVEL = 2;   // May 11, 2015
    int[] TRANSITIVITY_WEIGHT = { 3, 2, 1 };

    //int[] TRANSITIVITY_WEIGHT = {8,7,6,5,4,3,2,1};

    const int MAX_SLIDER_VAL = 10;  // An scale, while the actual depends on the number of traffics

    // Many of them are for the simulation input //
    const int ISOLATION = 50;   // In Percentage based on hosts
    const int USABILITY = 50;   // In Percentage based on hosts
    const int COST = 28;        // In Percentage based on routers
    //const int COST = 20;

    const int MAX_DEV_COST = 20;   // Maximum price/Cost possible for a device

    const int MAX_REACH_REQUIREMENTS = 20;  // In Percentage based on hosts. A node might have maximum this number of reachability requirement

    const double INCREASE_IN_ISOLATION = 2;    // To Tune the security policy (In Percentage)    
                                               ////////////////////////////////

    #endregion

    #region Pseudo Constants

    const int MAX_ROUTES = 5;

    int DIV_LEVEL = 6;

    int MAX_ISOLATION;
    int MAX_DIVERSITY;
    int MAX_RESILIENCY;     // May 11, 2015
    //int MAX_USABILITY;

    int MAX_ISO_USABILITY;
    int MAX_DIV_USABILITY;

    int ISOLATION_WEIGHT = (int)(0.7 * MAX_SLIDER_VAL);           // With respect to Scale of MAX_SLIDER_VAL
    int DIVERSITY_WEIGHT = (int)(0.3 * MAX_SLIDER_VAL);           // Scale of MAX_SLIDER_VAL (1 - ISOLATION_WEIGHT)

    int ISO_USABILITY_WEIGHT = (int)(0.7 * MAX_SLIDER_VAL);       // With respect to Scale of MAX_SLIDER_VAL
    int DIV_USABILITY_WEIGHT = (int)(0.3 * MAX_SLIDER_VAL);       // Scale of MAX_SLIDER_VAL (1 - ISO_USABILITY_WEIGHT)

    int MAX_TOTAL_RESILIENCY;
    int MAX_TOTAL_USABILITY;

    int DIFF_OS_DIFF_FAMILY_DIFF_SERV_DIVERSITY;  // Hard coded
    int DIFF_OS_DIFF_FAMILY_SAME_SERV_DIVERSITY;
    int DIFF_OS_SAME_FAMILY_DIFF_SERV_DIVERSITY;
    int DIFF_OS_SAME_FAMILY_SAME_SERV_DIVERSITY;
    int SAME_OS_DIFF_SERV_DIVERSITY;
    int SAME_OS_SAME_SERV_DIVERSITY;
    #endregion

    #region SMT Variables
    RealExpr[] IsoWgt, IsoUsa, DevCost;  // For each security isolation (security device)    
    RealExpr[] OSUsa, OSCost;
    IntExpr[] OSFamily;  // For each operating system

    RealExpr[] HIso, HDiv, HRes, HIsoUsa, HDivUsa, HResUsa, HOSCost;              // For each Host    

    IntExpr[] HOS, HOSFamily;       // The operating system selected for the system
    BoolExpr[,] HServ;              // Multiple services can run on the same machine
    RealExpr[,] FlowDiv;            // For each host pair (can be corresponded to a flow)

    RealExpr[,,] FlowRes;          // For each host pair at different transivitiy levels // May 11, 2015
    RealExpr[,] FlowResUltimate;    // For each host pair // May 11, 2015

    BoolExpr[,] Reachable;          // For each flow
    IntExpr[,] FlowIsoMsr;
    RealExpr[,] FlowIso, FlowIsoUsa;
    RealExpr[,] LinkDevCost;        // For each flow            
    BoolExpr[,] DevInLink;          // Per link per security device
    IntExpr[,,] DevInFlowRoute;    // For each flow and each route
    IntExpr[,] DevInAllFlowRoutes;  // For each flow

    RealExpr Usability, Resiliency, Cost;    // Total Usability, Cost, Resiliency    

    IntExpr IZero, IOne;
    RealExpr RZero, ROne;
    #endregion

    #region Input/Output Variables
    int nDev, nHost, nRouter, nLink;
    int nOS, nOSFamily, nServ;
    int cRes, cUsa, cCost, maxRes, maxUsa;
    //double factorIso;    // Ratio between Diversity Score and Isolation Score
    //double factorIsoUsa;    // Ratio between Diversity Usability Score and Isolation Usability Score

    static double res, usa, cost;
    //int cNIso, cNUsa; // The reductions of Isolation and usability    

    int[,] flowRank, reachReq;

    int[,] servReq;

    int[,] links;   // Links    

    //int maxResiliency;

    bool bSat;  // If there is a satisfiable model?
    #endregion

    static String fIn = String.Format("Input_R_{0}_{1}_{2}.txt", NUM_OF_HOST, NUM_OF_ROUTER, NUM_OF_LINK);
    static String fIn2 = String.Format("Input_R_{0}_{1}_{2}.txt", NUM_OF_HOST, NUM_OF_ROUTER, NUM_OF_LINK);


    #region Utility functions
    // Returns the factorial of n
    int factorial(int n)
    {
        int i;
        int res = 1;

        for (i = 2; i <= n; i++)
            res = res * i;

        return res;
    }

    // Returns the number of combinations by taking r items from n items
    int nCr(int n, int r)
    {
        int i;
        int res = 1;

        for (i = 1; i <= r; i++)
            res = res * (n - i + 1) / i;

        return res;
    }
    #endregion

    #region To search (possible) paths for a flow

    const int MAX_PATH_LEN = 20;

    int nPath;
    int[] path = new int[MAX_PATH_LEN];

    // Find the path
    void findPath(int dest, int len)
    {
        int i, j;
        String str;

        if (links[path[len - 1], dest] > 0) // Destination is reached
        {
            nPath++;

            path[len++] = dest;

            str = String.Format("DevInFlowRoute_{0}_{1}_{2}", path[0], dest, nPath);
            DevInFlowRoute[path[0], dest, nPath] = (IntExpr)z3.MkConst(str, z3.IntSort);

            IntExpr devInFlowRoute = DevInFlowRoute[path[0], dest, nPath];

            #region At most, each of the device types can be deployed on a link
            {
                BoolExpr body = z3.MkAnd(z3.MkGe(devInFlowRoute, IZero), z3.MkLe(devInFlowRoute, z3.MkInt(nDev)));

                slvr.Assert(body);
                twOut.WriteLine("{0}", body.ToString());
            }
            #endregion

            #region Security Device Deployment or Placement
            // Firewall and IDS
            {
                BoolExpr[] cond = new BoolExpr[len - 1];

                for (j = 1; j <= nDev; j++)
                {
                    if (j == 2) // IPSec is excluded
                        continue;

                    for (i = 0; i < (len - 1); i++)
                    {
                        cond[i] = DevInLink[links[path[i], path[i + 1]], j];
                    }

                    BoolExpr body = z3.MkImplies(z3.MkEq(DevInFlowRoute[path[0], dest, nPath], z3.MkNumeral(j, z3.IntSort)), z3.MkOr(cond));
                    slvr.Assert(body);
                    twOut.WriteLine("{0}", body.ToString());
                }
            }

            // IPSec
            {
                if (len >= 4)
                {
                    BoolExpr[] cond2 = new BoolExpr[2];

                    cond2[0] = z3.MkOr(DevInLink[links[path[0], path[1]], 2], DevInLink[links[path[1], path[2]], 2]);
                    cond2[1] = z3.MkOr(DevInLink[links[path[len - 2], path[len - 1]], 2], DevInLink[links[path[len - 3], path[len - 2]], 2]);

                    BoolExpr body = z3.MkImplies(z3.MkEq(DevInFlowRoute[path[0], dest, nPath], z3.MkNumeral(2, z3.IntSort)), z3.MkAnd(cond2));
                    slvr.Assert(body);
                    twOut.WriteLine("{0}", body.ToString());
                }
                else if (len >= 2)
                {
                    BoolExpr[] cond2 = new BoolExpr[2];

                    cond2[0] = DevInLink[links[path[0], path[1]], 2];
                    cond2[1] = DevInLink[links[path[len - 2], path[len - 1]], 2];

                    BoolExpr body = z3.MkImplies(z3.MkEq(DevInFlowRoute[path[0], dest, nPath], z3.MkNumeral(2, z3.IntSort)), z3.MkAnd(cond2));
                    slvr.Assert(body);
                    twOut.WriteLine("{0}", body.ToString());
                }
                else
                {
                    BoolExpr body = z3.MkNot(z3.MkEq(DevInFlowRoute[path[0], dest, nPath], z3.MkNumeral(2, z3.IntSort)));
                    slvr.Assert(body);
                    twOut.WriteLine("{0}", body.ToString());
                }
            }
            #endregion
        }
        else // Looking for other paths
        {
            for (i = nHost + 1; i <= (nHost + nRouter); i++)
            {
                for (j = 0; j < len; j++)
                {
                    if (path[j] == i)
                        break;
                }

                if ((j == len) && (links[path[len - 1], i] > 0))
                {
                    path[len] = i;
                    findPath(dest, len + 1);
                }
            }
        }
    }

    // Get the path from src to dest
    void getPath(int src, int dest)
    {
        path[0] = src;
        findPath(dest, 1);
    }

    #endregion


    // Read input from the file
    void ReadInput()
    {
        String str;
        String line;
        String[] words;

        int i, j, k;

        //BoolExpr[] args = new BoolExpr[2];
        char[] delims = { ' ', ',', '\t' };

        try
        {
            ////////// Preliminary Initialization //////////            
            IZero = z3.MkInt(0);
            IOne = z3.MkInt(1);

            RZero = z3.MkReal(0);
            ROne = z3.MkReal(1);

            Usability = (RealExpr)z3.MkRealConst("Usability");
            Resiliency = (RealExpr)z3.MkRealConst("Resiliency");
            Cost = (RealExpr)z3.MkRealConst("Cost");


            ////////// Read Input and Corresponding Declarations //////////
            System.IO.StreamReader file2 = new System.IO.StreamReader("Input_R_DPO.txt");

            #region Specifications on Isolation, Diversity, Usability, Deployment Cost
            // NOTE: Scoring the isolation patterns (security devices) from the partial orders is not in use at this moment

            #region Isolation based inputs

            #region Network isolation specifications
            // Primitive isolation patterns only (one to one matching between the isolation patterns and security device types)
            while (true)
            {
                if ((line = file2.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                nDev = Convert.ToInt32(words[0]);

                IsoWgt = new RealExpr[nDev + 1];
                IsoUsa = new RealExpr[nDev + 1];
                DevCost = new RealExpr[nDev + 1];
                //for (i = 0; i <= nDev; i++)
                //{
                //    str = String.Format("IsoWgt_{0}", i);
                //    IsoWgt[i] = (IntExpr)z3.MkConst(str, z3.IntSort);
                //    str = String.Format("IsoUsa_{0}", i);
                //    IsoUsa[i] = (IntExpr)z3.MkConst(str, z3.IntSort);
                //    str = String.Format("DevCost_{0}", i);
                //    DevCost[i] = (IntExpr)z3.MkConst(str, z3.IntSort);
                //}

                //MAX_ISO_USABILITY = nDev;

                break;
            }

            //// Partial order of isolation capability in terms of the resistance
            //int nPO;    // Given Partial Orders
            //while (true)
            //{
            //    if ((line = file2.ReadLine()) == null)
            //    {
            //        throw new Exception("Exit due to Insufficient/Extra Input");
            //    }

            //    line = line.Trim();
            //    if ((line.Length == 0) || line.StartsWith("#"))
            //        continue;

            //    words = line.Split(delims);
            //    if (words.Length != 1)
            //    {
            //        throw new Exception("Exit due to Insufficient/Extra Input");
            //    }

            //    nPO = Convert.ToInt32(words[0]);
            //    break;
            //}            

            //for (i = 0; i < nPO; i++)
            //{
            //    while (true)
            //    {
            //        if ((line = file2.ReadLine()) == null)
            //        {
            //            Console.WriteLine("Exit due to Insufficient/Extra Input");
            //            Environment.Exit(0);
            //        }

            //        line = line.Trim();
            //        if ((line.Length == 0) || line.StartsWith("#"))
            //            continue;

            //        words = line.Split(delims);
            //        if (words.Length != 3)
            //        {
            //            throw new Exception("Exit due to Insufficient/Extra Input");
            //        }

            //        // TODO: Write code (then comment the assignment beginning of this part)
            //        //
            //        //

            //        break;
            //    }
            //}

            //// Hard coded scores of the isolation patterns
            //slvr.Assert(z3.MkEq(IsoWgt[0], IZero));  // If no isolation is considered
            //slvr.Assert(z3.MkEq(IsoWgt[1], z3.MkInt(3)));
            //slvr.Assert(z3.MkEq(IsoWgt[2], z3.MkInt(2)));
            //slvr.Assert(z3.MkEq(IsoWgt[3], z3.MkInt(1)));                       

            // Maximum isolation
            while (true)
            {
                if ((line = file2.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                MAX_ISOLATION = Convert.ToInt32(words[0]);

                break;
            }

            //slvr.Assert(z3.MkEq(IsoWgt[0], IZero));  // If no isolation is considered
            IsoWgt[0] = RZero;  // If no isolation is considered

            // Isolation with respect to the deployment of an isolation pattern            
            {
                while (true)
                {
                    if ((line = file2.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient/Extra Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    words = line.Split(delims);
                    if (words.Length != nDev)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input");
                    }

                    for (i = 1; i <= nDev; i++)
                    {
                        //slvr.Assert(z3.MkEq(IsoWgt[i], z3.MkInt(Convert.ToInt32(words[i - 1]))));
                        IsoWgt[i] = z3.MkReal(Convert.ToInt32(words[i - 1]));
                    }

                    break;
                }
            }
            #endregion

            #region Usability specifications based on network isolations
            // Maximum usability
            while (true)
            {
                if ((line = file2.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                MAX_ISO_USABILITY = Convert.ToInt32(words[0]);
                //slvr.Assert(z3.MkEq(IsoUsa[0], z3.MkInt(MAX_ISO_USABILITY)));  // When no isolation is considered
                IsoUsa[0] = z3.MkReal(MAX_ISO_USABILITY);

                break;
            }

            // Usability with respect to the deployment of an isolation pattern
            //for (i = 1; i <= nDev; i++)
            {
                while (true)
                {
                    if ((line = file2.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient/Extra Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    words = line.Split(delims);
                    if (words.Length != nDev)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input");
                    }

                    for (i = 1; i <= nDev; i++)
                    {
                        //slvr.Assert(z3.MkEq(IsoUsa[i], z3.MkInt(Convert.ToInt32(words[i - 1]))));
                        IsoUsa[i] = z3.MkReal(Convert.ToInt32(words[i - 1]));
                    }

                    break;
                }
            }
            #endregion

            #region Cost specifications for network isolations
            // Cost for deploying a isolation pattern
            //slvr.Assert(z3.MkEq(DevCost[0], IZero));  // If no isolation is considered
            DevCost[0] = RZero;
            //for (i = 1; i <= nDev; i++)
            {
                while (true)
                {
                    if ((line = file2.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient/Extra Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    words = line.Split(delims);
                    if (words.Length != nDev)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input");
                    }

                    for (i = 1; i <= nDev; i++)
                    {
                        //slvr.Assert(z3.MkEq(DevCost[i], z3.MkNumeral(Convert.ToInt32(words[i - 1]), z3.IntSort)));
                        DevCost[i] = z3.MkReal(Convert.ToInt32(words[i - 1]));
                    }

                    break;
                }
            }
            #endregion

            #endregion

            #region Diversity based inputs

            #region Number of operating systems
            while (true)
            {
                if ((line = file2.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                nOS = Convert.ToInt32(words[0]);

                OSUsa = new RealExpr[nOS + 1];
                OSCost = new RealExpr[nOS + 1];
                OSFamily = new IntExpr[nOS + 1];
                //for (i = 1; i <= nOS; i++)
                //{
                //    str = String.Format("OSUsa_{0}", i);
                //    OSUsa[i] = (IntExpr)z3.MkConst(str, z3.IntSort);
                //    str = String.Format("OSCost_{0}", i);
                //    OSCost[i] = (IntExpr)z3.MkConst(str, z3.IntSort);
                //    str = String.Format("OSFamily_{0}", i);
                //    OSFamily[i] = (IntExpr)z3.MkConst(str, z3.IntSort);
                //}                

                break;
            }
            #endregion

            #region Families of operating systems
            while (true)
            {
                if ((line = file2.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                nOSFamily = Convert.ToInt32(words[0]);
                break;
            }

            for (i = 1; i <= nOSFamily; i++)
            {
                while (true)
                {
                    if ((line = file2.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient/Extra Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    words = line.Split(delims);
                    if (words.Length > (nOS - nOSFamily + 1))
                    {
                        throw new Exception("Exit due to Extra Input");
                    }

                    for (j = 0; j < words.Length; j++)
                    {
                        k = Convert.ToInt32(words[j]);
                        //slvr.Assert(z3.MkEq(OSFamily[k], z3.MkInt(i)));
                        OSFamily[k] = z3.MkInt(i);
                    }

                    break;
                }
            }
            #endregion

            #region OS Diversity
            // Maximum diversity
            while (true)
            {
                if ((line = file2.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                MAX_DIVERSITY = Convert.ToInt32(words[0]);

                break;
            }

            while (true)
            {
                if ((line = file2.ReadLine()) == null)
                {
                    Console.WriteLine("Exit due to Insufficient/Extra Input");
                    Environment.Exit(0);
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != DIV_LEVEL)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                DIFF_OS_DIFF_FAMILY_DIFF_SERV_DIVERSITY = Convert.ToInt32(words[0]);
                DIFF_OS_DIFF_FAMILY_SAME_SERV_DIVERSITY = Convert.ToInt32(words[1]);
                DIFF_OS_SAME_FAMILY_DIFF_SERV_DIVERSITY = Convert.ToInt32(words[2]);
                DIFF_OS_SAME_FAMILY_SAME_SERV_DIVERSITY = Convert.ToInt32(words[3]);
                SAME_OS_DIFF_SERV_DIVERSITY = Convert.ToInt32(words[4]);
                SAME_OS_SAME_SERV_DIVERSITY = Convert.ToInt32(words[5]);

                break;
            }
            #endregion

            #region Usability specifications based on diversity
            // Maximum Usability
            while (true)
            {
                if ((line = file2.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                MAX_DIV_USABILITY = Convert.ToInt32(words[0]);

                break;
            }

            // Usability with respect to the installation of an OS
            while (true)
            {
                if ((line = file2.ReadLine()) == null)
                {
                    Console.WriteLine("Exit due to Insufficient/Extra Input");
                    Environment.Exit(0);
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != nOS)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                for (i = 1; i <= nOS; i++)
                {
                    //slvr.Assert(z3.MkEq(OSUsa[i], z3.MkInt(Convert.ToInt32(words[i - 1]))));
                    OSUsa[i] = z3.MkReal(Convert.ToInt32(words[i - 1]));
                }

                break;
            }
            #endregion

            #region Cost specifications for operating sytems' installations
            while (true)
            {
                if ((line = file2.ReadLine()) == null)
                {
                    Console.WriteLine("Exit due to Insufficient/Extra Input");
                    Environment.Exit(0);
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != nOS)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                for (i = 1; i <= nOS; i++)
                {
                    //slvr.Assert(z3.MkEq(OSCost[i], z3.MkInt(Convert.ToInt32(words[i - 1]))));
                    OSCost[i] = z3.MkReal(Convert.ToInt32(words[i - 1]));
                }

                break;
            }
            #endregion

            #region Number of services
            while (true)
            {
                if ((line = file2.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                nServ = Convert.ToInt32(words[0]);

                break;
            }
            #endregion

            #endregion

            #endregion

            file2.Close();

            System.IO.StreamReader file = new System.IO.StreamReader(fIn);



            #region Number of hosts
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                nHost = Convert.ToInt32(words[0]);

                ////////// Initialization //////////
                HIso = new RealExpr[nHost + 1];
                HIsoUsa = new RealExpr[nHost + 1];

                HDiv = new RealExpr[nHost + 1];
                HDivUsa = new RealExpr[nHost + 1];

                HRes = new RealExpr[nHost + 1];
                HResUsa = new RealExpr[nHost + 1];

                HOS = new IntExpr[nHost + 1];
                HOSFamily = new IntExpr[nHost + 1];
                HOSCost = new RealExpr[nHost + 1];
                HServ = new BoolExpr[nHost + 1, nServ + 1];

                Reachable = new BoolExpr[nHost + 1, nHost + 1];
                FlowIsoMsr = new IntExpr[nHost + 1, nHost + 1];

                FlowIso = new RealExpr[nHost + 1, nHost + 1];
                FlowDiv = new RealExpr[nHost + 1, nHost + 1];
                FlowRes = new RealExpr[nHost + 1, nHost + 1, TRANSITIVITY_LEVEL + 1];    // May 11, 2015

                FlowResUltimate = new RealExpr[nHost + 1, nHost + 1];    // May 11, 2015

                FlowIsoUsa = new RealExpr[nHost + 1, nHost + 1];
                DevInAllFlowRoutes = new IntExpr[nHost + 1, nHost + 1];
                DevInFlowRoute = new IntExpr[nHost + 1, nHost + 1, MAX_ROUTES + 1];

                for (i = 1; i <= nHost; i++)
                {
                    str = String.Format("HIso_{0}", i);
                    HIso[i] = (RealExpr)z3.MkRealConst(str);

                    str = String.Format("HDiv_{0}", i);
                    HDiv[i] = (RealExpr)z3.MkRealConst(str);

                    str = String.Format("HRes_{0}", i);
                    HRes[i] = (RealExpr)z3.MkRealConst(str);

                    str = String.Format("HIsoUsa_{0}", i);
                    HIsoUsa[i] = (RealExpr)z3.MkRealConst(str);

                    str = String.Format("HDivUsa_{0}", i);
                    HDivUsa[i] = (RealExpr)z3.MkRealConst(str);

                    str = String.Format("HResUsa_{0}", i);
                    HResUsa[i] = (RealExpr)z3.MkRealConst(str);

                    str = String.Format("HOS_{0}", i);
                    HOS[i] = (IntExpr)z3.MkConst(str, z3.IntSort);

                    str = String.Format("HOSFamily_{0}", i);
                    HOSFamily[i] = (IntExpr)z3.MkConst(str, z3.IntSort);

                    str = String.Format("HOSCost_{0}", i);
                    HOSCost[i] = (RealExpr)z3.MkRealConst(str);

                    for (j = 1; j <= nServ; j++)
                    {
                        str = String.Format("HServ_{0}_{1}", i, j);
                        HServ[i, j] = (BoolExpr)z3.MkConst(str, z3.BoolSort);
                    }

                    for (j = 1; j <= nHost; j++)
                    {
                        str = String.Format("Reachable_{0}_{1}", i, j);
                        Reachable[i, j] = (BoolExpr)z3.MkConst(str, z3.BoolSort);
                        if (i == j)
                            slvr.Assert(Reachable[i, j]);

                        str = String.Format("FlowIsoMsr_{0}_{1}", i, j);
                        FlowIsoMsr[i, j] = (IntExpr)z3.MkConst(str, z3.IntSort);
                        if (i == j)
                            slvr.Assert(z3.MkEq(FlowIsoMsr[i, j], IZero));

                        str = String.Format("FlowIso_{0}_{1}", i, j);
                        FlowIso[i, j] = (RealExpr)z3.MkRealConst(str);

                        str = String.Format("FlowDiv_{0}_{1}", i, j);
                        FlowDiv[i, j] = (RealExpr)z3.MkRealConst(str);

                        for (k = 0; k <= TRANSITIVITY_LEVEL; k++)
                        {
                            str = String.Format("FlowRes_{0}_{1}_{2}", i, j, k);
                            FlowRes[i, j, k] = (RealExpr)z3.MkRealConst(str);
                        }

                        str = String.Format("FlowResUltimate_{0}_{1}", i, j);
                        FlowResUltimate[i, j] = (RealExpr)z3.MkRealConst(str);

                        str = String.Format("FlowIsoUsa_{0}_{1}", i, j);
                        FlowIsoUsa[i, j] = (RealExpr)z3.MkRealConst(str);

                        str = String.Format("DevInAllFlowRoutes_{0}_{1}", i, j);
                        DevInAllFlowRoutes[i, j] = (IntExpr)z3.MkConst(str, z3.IntSort);
                        if (i == j)
                            slvr.Assert(z3.MkEq(DevInAllFlowRoutes[i, j], IZero));
                    }
                }

                break;
            }
            #endregion

            #region Topology (Routers and links)
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Links");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Links");
                }

                nRouter = Convert.ToInt32(words[0]);

                break;
            }

            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Links");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Links");
                }

                nLink = Convert.ToInt32(words[0]);

                DevInLink = new BoolExpr[nLink + 1, nDev + 1];
                LinkDevCost = new RealExpr[nLink + 1, nDev + 1];

                for (i = 1; i <= nLink; i++)
                    for (j = 0; j <= nDev; j++)
                    {
                        str = String.Format("DevInLink_{0}_{1}", i, j);
                        DevInLink[i, j] = (BoolExpr)z3.MkConst(str, z3.BoolSort);

                        str = String.Format("LinkDevCost_{0}_{1}", i, j);
                        LinkDevCost[i, j] = (RealExpr)z3.MkRealConst(str);
                    }

                break;
            }

            //links = new int[nHost + nRouter + 1, nHost + nRouter + 1];
            links = new int[nHost + nRouter + 1, nHost + nRouter + 1];
            for (i = 1; i <= (nHost + nRouter); i++)
                for (j = 1; j <= (nHost + nRouter); j++)
                    links[i, j] = 0;

            for (i = 1; i <= nLink; i++)
            {
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: Links");
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    words = line.Split(delims);
                    if (words.Length != 2)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: Links");
                    }

                    links[Convert.ToInt32(words[0]), Convert.ToInt32(words[1])] = i;
                    links[Convert.ToInt32(words[1]), Convert.ToInt32(words[0])] = i;

                    break;
                }
            }
            #endregion

            #region Reachability requirements
            reachReq = new int[nHost + 1, nHost + 1];
            for (i = 1; i <= nHost; i++)
                for (j = 1; j <= nHost; j++)
                    reachReq[i, j] = 0;

            for (i = 1; i <= nHost; i++)
            {
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient/Extra Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    words = line.Split(delims);
                    for (j = 0; j < (words.Length - 1); j++)
                    {
                        //k = Convert.ToInt32(words[j]);
                        reachReq[i, Convert.ToInt32(words[j])] = 1;
                        slvr.Assert(Reachable[i, Convert.ToInt32(words[j])]);
                    }

                    break;
                }
            }
            #endregion

            #region Ranks of the flow (usability)
            int nHighRanks;
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Links");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Links");
                }

                nHighRanks = Convert.ToInt32(words[0]);

                break;
            }

            flowRank = new int[nHost + 1, nHost + 1];
            for (i = 1; i <= nHost; i++)
                for (j = 1; j <= nHost; j++)
                {
                    if (reachReq[i, j] == 1)
                        flowRank[i, j] = MAX_ISO_USABILITY; // Max usability
                    else
                        flowRank[i, j] = 1; // Min usability
                }

            for (i = 1; i <= nHighRanks; i++)
            {
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: Links");
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    words = line.Split(delims);
                    if (words.Length != 3)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: Links");
                    }

                    flowRank[Convert.ToInt32(words[0]), Convert.ToInt32(words[1])] = Convert.ToInt32(words[2]);

                    break;
                }
            }
            #endregion

            #region Service requirements
            servReq = new int[nHost + 1, nServ + 1];
            for (i = 1; i <= nHost; i++)
                for (j = 1; j <= nServ; j++)
                    servReq[i, j] = 0;

            for (i = 1; i <= nHost; i++)
            {
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient/Extra Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    words = line.Split(delims);
                    for (j = 0; j < (words.Length - 1); j++)
                    {
                        //k = Convert.ToInt32(words[j]);
                        servReq[i, Convert.ToInt32(words[j])] = 1;
                        slvr.Assert(HServ[i, Convert.ToInt32(words[j])]);
                    }

                    break;
                }
            }
            #endregion

            #region Sliders' Input
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 3)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input");
                }

                ISOLATION_WEIGHT = (ISOLATION_WEIGHT * MAX_DIVERSITY) / MAX_ISOLATION;

                MAX_RESILIENCY = MAX_ISOLATION * ISOLATION_WEIGHT + MAX_DIVERSITY * DIVERSITY_WEIGHT;
                maxRes = 0;

                for (i = 0; i <= TRANSITIVITY_LEVEL; i++)
                    maxRes += (int)(nCr(nHost, 2) * factorial(2) * MAX_RESILIENCY * TRANSITIVITY_WEIGHT[i]);
                MAX_TOTAL_RESILIENCY = maxRes;

                res = Convert.ToDouble(words[0]);
                cRes = (int)(Convert.ToDouble(words[0]) * maxRes / MAX_SLIDER_VAL);

                int maxIsoUsa = 0;
                // This is for flow ranks
                for (i = 1; i <= nHost; i++)
                    for (j = 1; j <= nHost; j++)
                    {
                        if (i == j)
                            continue;

                        maxIsoUsa += MAX_ISO_USABILITY * flowRank[i, j];
                    }
                //////////
                double avgIsoUsaFlow = (double)maxIsoUsa / (nCr(nHost, 2) * factorial(2));

                ISO_USABILITY_WEIGHT = (int)((ISO_USABILITY_WEIGHT * MAX_DIV_USABILITY) / avgIsoUsaFlow);

                maxUsa = (int)(nCr(nHost, 2) * factorial(2) * (MAX_ISO_USABILITY * ISO_USABILITY_WEIGHT + MAX_DIV_USABILITY * DIV_USABILITY_WEIGHT));

                MAX_TOTAL_USABILITY = maxUsa;

                usa = Convert.ToDouble(words[1]);
                cUsa = (int)(Convert.ToDouble(words[1]) * maxUsa / MAX_SLIDER_VAL);

                cCost = Convert.ToInt32(words[2]);
                cost = Convert.ToInt32(words[2]);

                twOut.WriteLine("Constraints: {0} {1} {2}", cRes, cUsa, cCost);
                twData.WriteLine("Constraints: {0} {1} {2}", cRes, cUsa, cCost);

                break;
            }
            #endregion

            file.Close();
        }
        catch (Exception exp)
        {
            throw exp;
        }
    }
    void SimulateInputTree()
    {
        int i, j, k, l;

        System.IO.StreamWriter file = new System.IO.StreamWriter(fIn);
        Random random = new Random(DateTime.Now.Millisecond);

        #region hosts, routers, and links
        file.WriteLine("# Number of Hosts");
        file.WriteLine("{0}", NUM_OF_HOST);
        file.WriteLine();

        file.WriteLine("# Number of Routers");
        file.WriteLine("{0}", NUM_OF_ROUTER);
        file.WriteLine();

        i = NUM_OF_HOST + NUM_OF_ROUTER; // Number of links
        file.WriteLine("# Number of Links");
        file.WriteLine("{0}", i);

        for (i = 1; i <= NUM_OF_HOST; i++) //
        {
            j = random.Next(1, NUM_OF_ROUTER + 1) + NUM_OF_HOST;
            file.WriteLine("{0} {1}", i, j);
        }

        for (i = NUM_OF_HOST + 1; i < (NUM_OF_HOST + NUM_OF_ROUTER); i++)
        {
            j = random.Next(i + 1, NUM_OF_HOST + NUM_OF_ROUTER + 1);
            file.WriteLine("{0} {1}", i, j);
        }

        i = random.Next(1, NUM_OF_ROUTER + 1) + NUM_OF_HOST;
        do
        {
            j = random.Next(1, NUM_OF_ROUTER + 1) + NUM_OF_HOST;
        } while (i == j);

        file.WriteLine("{0} {1}", i, j);
        file.WriteLine();
        #endregion



        //#region Sliders' values
        //i = ISOLATION * MAX_SLIDER_VAL / 100;
        //j = USABILITY * MAX_SLIDER_VAL / 100;
        //k = COST * (NUM_OF_ROUTER + (NUM_OF_HOST / NUM_OF_ROUTER)) * MAX_DEV_COST / 100;

        //file.WriteLine("# Sliders' Values (Isolation, Usability, Cost)");
        //file.WriteLine("{0} {1} {2}", i, j, k);
        //#endregion

        //file.Close();

        #region Reachability requirements
        file.WriteLine("# Reachability Requirements");
        for (i = 1; i <= NUM_OF_HOST; i++)  // Within the same highway           
        {
            l = random.Next(1, NUM_OF_HOST + 1) * MAX_REACH_REQUIREMENTS / 100;
            for (j = 0; j < l; j++)
            {
                do
                {
                    k = random.Next(1, NUM_OF_HOST + 1);
                } while (k == i);

                file.Write("{0} ", k);
            }
            file.WriteLine("0");
        }
        file.WriteLine();
        #endregion

        //#region Reachability requirements
        //file.WriteLine("# Reachability Requirements");
        //for (i = 1; i <= NUM_OF_HOST; i++)  // Within the same highway           
        //{
        //    l = random.Next(1, NUM_OF_HOST + 1) * MAX_REACH_REQUIREMENTS / 100;
        //    for (j = 0; j < l; j++)
        //    {
        //        do
        //        {
        //            k = random.Next(1, NUM_OF_HOST + 1);
        //        } while (k == i);

        //        file.Write("{0} ", k);
        //    }
        //    file.WriteLine("0");
        //}
        //file.WriteLine();
        //#endregion

        #region Rank of the flows
        int myrank = random.Next(5, NUM_OF_HOST - 2);
        file.WriteLine("# Rank of the flows, which have higher rank than the default value (1)");
        file.WriteLine("{0}", myrank);
        for (i = 1; i <= myrank;)  // Within the same highway           
        {
            //while (true)
            //{
            int source = random.Next(1, NUM_OF_HOST);
            int destination = random.Next(1, NUM_OF_HOST);
            int rankoriginial = random.Next(2, 3); // otherwise 1

            if (source == destination)
                continue;
            else// this ensures that all routers have been used
            {
                file.WriteLine("{0} {1} {2}", source, destination, rankoriginial);
                i++;

            }
            //}
        }
        file.WriteLine();
        #endregion

        #region Service Requirements
        file.WriteLine("# Service requirements");
        for (i = 1; i <= NUM_OF_HOST; i++)
        {
            int numberOfService = random.Next(1, 3);
            int[] serviceArray = new int[numberOfService];

            int myJ = 1;
            for (; myJ <= numberOfService;)  // Within the same highway           
            {
                int myService = random.Next(1, 5);
                if (myJ == 1)
                {
                    file.Write("{0}", myService);
                    file.Write(" ");
                    serviceArray[myJ - 1] = myService;
                }
                else
                {
                    if (Array.Exists(serviceArray, element => element == myService))
                    {
                        continue;
                    }
                    file.Write("{0}", myService);
                    file.Write(" ");
                    serviceArray[myJ - 1] = myService;

                }
                myJ++;
            }
            file.Write("{0}", 0);
            file.WriteLine();
        }

        file.WriteLine();
        #endregion

        #region Sliders' values
        i = ISOLATION * MAX_SLIDER_VAL / 100;
        j = USABILITY * MAX_SLIDER_VAL / 100;
        //k = COST * (NUM_OF_ROUTER + (NUM_OF_HOST / NUM_OF_ROUTER)) * MAX_DEV_COST / 100;
        k = 100 * COST * (NUM_OF_ROUTER + (NUM_OF_HOST / NUM_OF_ROUTER)) * MAX_DEV_COST; // May 15


        file.WriteLine("# Sliders' Values (Resiliency, Usability, Cost)");
        file.WriteLine("{0} {1} {2}", i, j, k);
        #endregion
        file.WriteLine();

        file.Close();
    }
    void SimulateInputStarNew()
    {
        int i, j, k, l, centerRouter, otherRouter, iMy, linkCounter;
        int[] otherRouterArray = new int[NUM_OF_ROUTER - 1];

        System.IO.StreamWriter file = new System.IO.StreamWriter(fIn2);
        Random random = new Random(DateTime.Now.Millisecond);

        //hosts, routers, and links
        file.WriteLine("# Number of Hosts");
        file.WriteLine("{0}", NUM_OF_HOST);
        file.WriteLine();

        file.WriteLine("# Number of Routers");
        file.WriteLine("{0}", NUM_OF_ROUTER);
        file.WriteLine();

        i = NUM_OF_HOST + NUM_OF_ROUTER; // Number of links
        file.WriteLine("# Number of Links");
        file.WriteLine("{0}", i);
        centerRouter = random.Next(1, NUM_OF_ROUTER + 1) + NUM_OF_HOST;



        i = 1;
        linkCounter = 0;

        otherRouter = NUM_OF_HOST + 1;
        while (true)
        {
            //otherRouter = random.Next(1, NUM_OF_ROUTER + 1) + NUM_OF_HOST;
            //otherRouter = random.Next(1, NUM_OF_ROUTER + 1) + NUM_OF_HOST;
            if (otherRouter == NUM_OF_ROUTER + NUM_OF_HOST + 1)
                break;
            if (otherRouter == centerRouter)
            {
                otherRouter++;
                continue;
            }

            else// this ensures that all routers have been used
            {
                file.WriteLine("{0} {1}", otherRouter, centerRouter);
                otherRouter++;
                linkCounter++;
                i++;

            }
        }

        int hostPerRouter = NUM_OF_HOST / NUM_OF_ROUTER;
        int remHost = NUM_OF_HOST % NUM_OF_ROUTER;
        int routerCounter = NUM_OF_HOST + 1;
        int myHostCounter = 1;
        int perHostCounter = 0;
        while (true)
        {
            perHostCounter = 0;
            //linkCounter = 0;
            //if (routerCounter == NUM_OF_ROUTER - 1)
            if (myHostCounter == NUM_OF_HOST + 1)
            {
                break;
            }
            if (routerCounter == centerRouter)
            {
                routerCounter++;
                continue;
            }

            if (routerCounter > NUM_OF_ROUTER + NUM_OF_HOST)
            {
                routerCounter = NUM_OF_HOST + 1;
            }
            else
            {

                //while (perHostCounter != hostPerRouter)
                //{
                //perHostCounter++;

                file.WriteLine("{0} {1}", myHostCounter, routerCounter);
                routerCounter++;
                myHostCounter++;
                //otherRouter--;
                linkCounter++;

                //}

            }

        }

        while (true)
        {
            int lastSource = random.Next(1, NUM_OF_ROUTER + 1) + NUM_OF_HOST;
            int lastDestination = random.Next(1, NUM_OF_ROUTER + 1) + NUM_OF_HOST;
            if ((lastSource == lastDestination))
                continue;
            if (lastSource == centerRouter)
                continue;
            if (lastDestination == centerRouter)
                continue;

            else
            {
                file.WriteLine("{0} {1}", lastSource, lastDestination);
                break;
            }

        }

        file.WriteLine();

        //for (iMy = i; iMy <= NUM_OF_HOST + 1; iMy++)
        //{
        //    otherRouter = random.Next(1, NUM_OF_ROUTER + 1) + NUM_OF_HOST;
        //    file.WriteLine("{0} {1}", iMy, otherRouter);
        //}

        #region Reachability requirements
        file.WriteLine("# Reachability Requirements");
        for (i = 1; i <= NUM_OF_HOST; i++)  // Within the same highway           
        {
            l = random.Next(1, NUM_OF_HOST + 1) * MAX_REACH_REQUIREMENTS / 100;
            for (j = 0; j < l; j++)
            {
                do
                {
                    k = random.Next(1, NUM_OF_HOST + 1);
                } while (k == i);

                file.Write("{0} ", k);
            }
            file.WriteLine("0");
        }
        file.WriteLine();
        #endregion

        //#region Reachability requirements
        //file.WriteLine("# Reachability Requirements");
        //for (i = 1; i <= NUM_OF_HOST; i++)  // Within the same highway           
        //{
        //    l = random.Next(1, NUM_OF_HOST + 1) * MAX_REACH_REQUIREMENTS / 100;
        //    for (j = 0; j < l; j++)
        //    {
        //        do
        //        {
        //            k = random.Next(1, NUM_OF_HOST + 1);
        //        } while (k == i);

        //        file.Write("{0} ", k);
        //    }
        //    file.WriteLine("0");
        //}
        //file.WriteLine();
        //#endregion

        #region Rank of the flows
        int myrank = random.Next(5, NUM_OF_HOST - 2);
        file.WriteLine("# Rank of the flows, which have higher rank than the default value (1)");
        file.WriteLine("{0}", myrank);
        for (i = 1; i <= myrank;)  // Within the same highway           
        {
            //while (true)
            //{
            int source = random.Next(1, NUM_OF_HOST);
            int destination = random.Next(1, NUM_OF_HOST);
            int rankoriginial = random.Next(2, 3); // otherwise 1

            if (source == destination)
                continue;
            else// this ensures that all routers have been used
            {
                file.WriteLine("{0} {1} {2}", source, destination, rankoriginial);
                i++;

            }
            //}
        }
        file.WriteLine();
        #endregion

        #region Service Requirements
        file.WriteLine("# Service requirements");
        for (i = 1; i <= NUM_OF_HOST; i++)
        {
            int numberOfService = random.Next(1, 3);
            int[] serviceArray = new int[numberOfService];

            int myJ = 1;
            for (; myJ <= numberOfService;)  // Within the same highway           
            {
                int myService = random.Next(1, 5);
                if (myJ == 1)
                {
                    file.Write("{0}", myService);
                    file.Write(" ");
                    serviceArray[myJ - 1] = myService;
                }
                else
                {
                    if (Array.Exists(serviceArray, element => element == myService))
                    {
                        continue;
                    }
                    file.Write("{0}", myService);
                    file.Write(" ");
                    serviceArray[myJ - 1] = myService;

                }
                myJ++;
            }
            file.Write("{0}", 0);
            file.WriteLine();
        }

        file.WriteLine();
        #endregion

        #region Sliders' values
        i = ISOLATION * MAX_SLIDER_VAL / 100;
        j = USABILITY * MAX_SLIDER_VAL / 100;
        //k = COST * (NUM_OF_ROUTER + (NUM_OF_HOST / NUM_OF_ROUTER)) * MAX_DEV_COST / 100;
        k = 100 * COST * (NUM_OF_ROUTER + (NUM_OF_HOST / NUM_OF_ROUTER)) * MAX_DEV_COST; // May 15


        file.WriteLine("# Sliders' Values (Resiliency, Usability, Cost)");
        file.WriteLine("{0} {1} {2}", i, j, k);
        #endregion
        file.WriteLine();

        file.Close();
    }
    void SimulateInputStarLevel()
    {
        int i, j, k, l, centerRouter, otherRouter, otherCenterRouter, iMy, linkCounter = 0, otherCenterRouterCount, otherRouterCount;
        int[] otherRouterArray = new int[NUM_OF_ROUTER - 1];

        System.IO.StreamWriter file = new System.IO.StreamWriter(fIn2);
        Random random = new Random(DateTime.Now.Millisecond);

        //hosts, routers, and links
        file.WriteLine("# Number of Hosts");
        file.WriteLine("{0}", NUM_OF_HOST);
        file.WriteLine();

        file.WriteLine("# Number of Routers");
        file.WriteLine("{0}", NUM_OF_ROUTER);
        file.WriteLine();

        i = NUM_OF_HOST + NUM_OF_ROUTER - 1; // Number of links
        file.WriteLine("# Number of Links");
        file.WriteLine("{0}", i);
        centerRouter = NUM_OF_HOST + 1;
        otherCenterRouter = centerRouter + 1;
        otherCenterRouterCount = 1;

        while (otherCenterRouterCount != 5 || otherCenterRouterCount == NUM_OF_ROUTER - 1)
        {
            file.WriteLine("{0} {1}", otherCenterRouter, centerRouter);
            otherCenterRouter++;
            otherCenterRouterCount++;
            linkCounter++;
        }


        otherRouter = otherCenterRouter;
        otherCenterRouter = 2;

        while (otherRouter != NUM_OF_HOST + NUM_OF_ROUTER + 1)
        {
            file.WriteLine("{0} {1}", otherRouter, NUM_OF_HOST + otherCenterRouter);
            otherCenterRouter++;
            otherRouter++;
            linkCounter++;
            if (otherCenterRouter == 6)
            {
                otherCenterRouter = 2;
            }

        }



        int hostPerRouter = NUM_OF_HOST / (NUM_OF_ROUTER - 4 - 1);
        int remHost = NUM_OF_HOST % (NUM_OF_ROUTER - 4 - 1);
        int routerCounter = NUM_OF_HOST + 4 + 2;
        int myHostCounter = 1;
        int perHostCounter = 0;
        while (true)
        {
            perHostCounter = 0;
            //linkCounter = 0;
            //if (routerCounter == NUM_OF_ROUTER - 1)
            if (myHostCounter == NUM_OF_HOST + 1)
            {
                break;
            }
            //if (routerCounter == centerRouter)
            //{
            //    routerCounter++;
            //    continue;
            //}

            if (routerCounter > NUM_OF_ROUTER + NUM_OF_HOST)
            {
                routerCounter = NUM_OF_HOST + 2 + 4;
            }
            else
            {

                //while (perHostCounter != hostPerRouter)
                //{
                //perHostCounter++;

                file.WriteLine("{0} {1}", myHostCounter, routerCounter);
                routerCounter++;
                myHostCounter++;
                //otherRouter--;
                //linkCounter++;

                //}

            }

        }


        file.WriteLine();

        //for (iMy = i; iMy <= NUM_OF_HOST + 1; iMy++)
        //{
        //    otherRouter = random.Next(1, NUM_OF_ROUTER + 1) + NUM_OF_HOST;
        //    file.WriteLine("{0} {1}", iMy, otherRouter);
        //}

        #region Reachability requirements
        file.WriteLine("# Reachability Requirements");
        for (i = 1; i <= NUM_OF_HOST; i++)  // Within the same highway           
        {
            l = random.Next(1, NUM_OF_HOST + 1) * MAX_REACH_REQUIREMENTS / 100;
            for (j = 0; j < l; j++)
            {
                do
                {
                    k = random.Next(1, NUM_OF_HOST + 1);
                } while (k == i);

                file.Write("{0} ", k);
            }
            file.WriteLine("0");
        }
        file.WriteLine();
        #endregion

        //#region Reachability requirements
        //file.WriteLine("# Reachability Requirements");
        //for (i = 1; i <= NUM_OF_HOST; i++)  // Within the same highway           
        //{
        //    l = random.Next(1, NUM_OF_HOST + 1) * MAX_REACH_REQUIREMENTS / 100;
        //    for (j = 0; j < l; j++)
        //    {
        //        do
        //        {
        //            k = random.Next(1, NUM_OF_HOST + 1);
        //        } while (k == i);

        //        file.Write("{0} ", k);
        //    }
        //    file.WriteLine("0");
        //}
        //file.WriteLine();
        //#endregion

        #region Rank of the flows
        int myrank = random.Next(5, NUM_OF_HOST - 2);
        file.WriteLine("# Rank of the flows, which have higher rank than the default value (1)");
        file.WriteLine("{0}", myrank);
        for (i = 1; i <= myrank;)  // Within the same highway           
        {
            //while (true)
            //{
            int source = random.Next(1, NUM_OF_HOST);
            int destination = random.Next(1, NUM_OF_HOST);
            int rankoriginial = random.Next(2, 3); // otherwise 1

            if (source == destination)
                continue;
            else// this ensures that all routers have been used
            {
                file.WriteLine("{0} {1} {2}", source, destination, rankoriginial);
                i++;

            }
            //}
        }
        file.WriteLine();
        #endregion

        #region Service Requirements
        file.WriteLine("# Service requirements");
        for (i = 1; i <= NUM_OF_HOST; i++)
        {
            int numberOfService = random.Next(1, 3);
            int[] serviceArray = new int[numberOfService];

            int myJ = 1;
            for (; myJ <= numberOfService;)  // Within the same highway           
            {
                int myService = random.Next(1, 5);
                if (myJ == 1)
                {
                    file.Write("{0}", myService);
                    file.Write(" ");
                    serviceArray[myJ - 1] = myService;
                }
                else
                {
                    if (Array.Exists(serviceArray, element => element == myService))
                    {
                        continue;
                    }
                    file.Write("{0}", myService);
                    file.Write(" ");
                    serviceArray[myJ - 1] = myService;

                }
                myJ++;
            }
            file.Write("{0}", 0);
            file.WriteLine();
        }

        file.WriteLine();
        #endregion

        #region Sliders' values
        i = ISOLATION * MAX_SLIDER_VAL / 100;
        j = USABILITY * MAX_SLIDER_VAL / 100;
        //k = COST * (NUM_OF_ROUTER + (NUM_OF_HOST / NUM_OF_ROUTER)) * MAX_DEV_COST / 100;
        k = 100 * COST * (NUM_OF_ROUTER + (NUM_OF_HOST / NUM_OF_ROUTER)) * MAX_DEV_COST; // May 15


        file.WriteLine("# Sliders' Values (Resiliency, Usability, Cost)");
        file.WriteLine("{0} {1} {2}", i, j, k);
        #endregion
        file.WriteLine();

        file.Close();
    }
    // Modeling the system
    // Modeling the system
    void Model()
    {
        int i, j, k, l;

        try
        {
            Context.ToggleWarningMessages(true);
            //Log.Open("State Estimation Impact.log");

            Console.WriteLine("Resiliency ConfigSynthesizer: ");
            Console.Write("Z3 Major Version: ");
            Console.WriteLine(Microsoft.Z3.Version.Major.ToString());
            Console.Write("Z3 Full Version: ");
            Console.WriteLine(Microsoft.Z3.Version.ToString());

            // Earlier Z3 syntax
            //Dictionary<string, string> cfg = new Dictionary<string, string>() { 
            //        { "MODEL", "true"},                          
            //        { "SOFT_TIMEOUT", TIME_OUT}
            //    };

            // Latest Z3 syntax
            Dictionary<string, string> cfg = new Dictionary<string, string>() {
                    { "MODEL", "true"},
                    { "TIMEOUT", TIME_OUT}
                };
            //       SimulateInputStarNew();
            //SimulateInputStarLevel();
            //SimulateInputTree();
            using (z3 = new Context(cfg))
            {
                slvr = z3.MkSolver();

                ReadInput();

                #region Model                

                #region Isolation Scoring Model (Commented)

                #region Boundary checking for isolation weight(Commented as the isolation scores are hard coded)
                //{
                //    Term arg = z3.MkConst("n", z3.IntSort);
                //    Term func = z3.MkApp(IsoWgt, arg);

                //    Term cond = z3.MkAnd(z3.MkGt(arg, IZero), z3.MkLe(arg, z3.MkNumeral(nDev, z3.IntSort)));

                //    Term body = z3.MkImplies(cond, z3.MkAnd(z3.MkGt(func, IZero), z3.MkLe(func, z3.MkNumeral(nDev, z3.IntSort))));

                //    Term q = z3.MkForall(0, new Term[] { arg }, null, body);
                //    slvr.Assert(q);
                //    twOut.WriteLine("{0}", q.ToString());
                //}
                #endregion

                #endregion

                #region Isolation and Usability Model

                #region A reachability means that no isolation measure cannot be taken which has zero usability
                {
                    for (i = 1; i <= nHost; i++)
                        for (j = 1; j <= nHost; j++)
                        {
                            BoolExpr body = z3.MkImplies(Reachable[i, j], z3.MkNot(z3.MkEq(FlowIsoMsr[i, j], IOne)));

                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());
                        }
                }
                #endregion

                #region No reachability means that an isolation measure is taken which has zero usability
                {
                    for (i = 1; i <= nHost; i++)
                        for (j = 1; j <= nHost; j++)
                        {
                            BoolExpr body = z3.MkImplies(z3.MkNot(Reachable[i, j]), z3.MkEq(FlowIsoMsr[i, j], IOne));
                            //BoolExpr body = z3.MkImplies(z3.MkEq(FlowIsoMsr[i, j], IOne), z3.MkNot(Reachable[i, j]));

                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());
                        }
                }
                #endregion

                #region Constraints on flow isolations
                {
                    for (i = 1; i <= nHost; i++)
                        for (j = 1; j <= nHost; j++)
                        {
                            BoolExpr body = z3.MkAnd(z3.MkGe(FlowIsoMsr[i, j], IZero), z3.MkLe(FlowIsoMsr[i, j], z3.MkInt(nDev)));
                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());
                        }
                }
                #endregion

                #region For all flows, if flow isolation is a pattern, the isolation weight corresponds to the pattern
                {
                    for (i = 1; i <= nHost; i++)
                        for (j = 1; j <= nHost; j++)
                            for (k = 0; k <= nDev; k++)
                            {
                                BoolExpr body = z3.MkImplies(z3.MkEq(FlowIsoMsr[i, j], z3.MkInt(k)), z3.MkEq(FlowIso[i, j], IsoWgt[k]));
                                slvr.Assert(body);
                                twOut.WriteLine("{0}", body.ToString());
                            }

                    for (i = 1; i <= nHost; i++)
                        for (j = 1; j <= nHost; j++)
                            for (k = 0; k <= nDev; k++)
                            {
                                //BoolExpr body = z3.MkImplies(z3.MkEq(FlowIsoMsr[i, j], z3.MkInt(k)), z3.MkEq(FlowIsoUsa[i, j], IsoUsa[k]));
                                BoolExpr body = z3.MkImplies(z3.MkEq(FlowIsoMsr[i, j], z3.MkInt(k)), z3.MkEq(FlowIsoUsa[i, j],
                                    z3.MkMul(IsoUsa[k], z3.MkReal(flowRank[i, j]))));
                                slvr.Assert(body);
                                twOut.WriteLine("{0}", body.ToString());
                            }
                }
                #endregion

                #region Total Usability for a Host
                {
                    RealExpr[] termsUsa = new RealExpr[nHost - 1];

                    for (i = 1; i <= nHost; i++)
                    {
                        k = 0;

                        for (j = 1; j <= nHost; j++)
                        {
                            if (i == j)
                                continue;

                            termsUsa[k] = FlowIsoUsa[j, i];

                            k++;
                        }

                        BoolExpr body;

                        body = z3.MkEq(HIsoUsa[i], z3.MkAdd(termsUsa));
                        slvr.Assert(body);
                        twOut.WriteLine("{0}", body.ToString());
                    }
                }
                #endregion                

                #endregion

                #region Diversity Model

                #region Assignment of OS and OS Family to Each Host
                {
                    for (i = 1; i <= nHost; i++)
                    {
                        BoolExpr body = z3.MkAnd(z3.MkGe(HOS[i], IOne), z3.MkLe(HOS[i], z3.MkInt(nOS)));
                        slvr.Assert(body);
                        twOut.WriteLine("{0}", body.ToString());
                    }

                    for (i = 1; i <= nHost; i++)
                    {
                        for (j = 1; j <= nOS; j++)
                        {
                            BoolExpr body = z3.MkImplies(z3.MkEq(HOS[i], z3.MkInt(j)), z3.MkEq(HOSFamily[i], OSFamily[j]));
                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());
                        }
                    }
                }
                #endregion

                #region For All Flows, Find the Diversity
                {
                    for (i = 1; i <= nHost; i++)
                        for (j = 1; j <= nHost; j++)
                        {
                            if (i == j)
                                continue;

                            BoolExpr[] Exprs = new BoolExpr[nServ];
                            for (k = 1; k <= nServ; k++)
                            {
                                Exprs[k - 1] = z3.MkAnd(HServ[i, k], HServ[j, k]);
                            }

                            BoolExpr body = z3.MkImplies(z3.MkAnd(Reachable[i, j], z3.MkNot(z3.MkEq(HOSFamily[i], HOSFamily[j])), z3.MkNot(z3.MkOr(Exprs))),
                                z3.MkEq(FlowDiv[i, j], z3.MkReal(DIFF_OS_DIFF_FAMILY_DIFF_SERV_DIVERSITY)));
                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());

                            body = z3.MkImplies(z3.MkAnd(Reachable[i, j], z3.MkNot(z3.MkEq(HOSFamily[i], HOSFamily[j])), z3.MkOr(Exprs)),
                                z3.MkEq(FlowDiv[i, j], z3.MkReal(DIFF_OS_DIFF_FAMILY_SAME_SERV_DIVERSITY)));
                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());

                            body = z3.MkImplies(z3.MkAnd(Reachable[i, j], z3.MkEq(HOSFamily[i], HOSFamily[j]), z3.MkNot(z3.MkEq(HOS[i], HOS[j])), z3.MkNot(z3.MkOr(Exprs))),
                                z3.MkEq(FlowDiv[i, j], z3.MkReal(DIFF_OS_SAME_FAMILY_DIFF_SERV_DIVERSITY)));
                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());

                            body = z3.MkImplies(z3.MkAnd(Reachable[i, j], z3.MkEq(HOSFamily[i], HOSFamily[j]), z3.MkNot(z3.MkEq(HOS[i], HOS[j])), z3.MkOr(Exprs)),
                                z3.MkEq(FlowDiv[i, j], z3.MkReal(DIFF_OS_SAME_FAMILY_SAME_SERV_DIVERSITY)));
                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());

                            body = z3.MkImplies(z3.MkAnd(Reachable[i, j], z3.MkEq(HOS[i], HOS[j]), z3.MkNot(z3.MkOr(Exprs))),
                                z3.MkEq(FlowDiv[i, j], z3.MkReal(SAME_OS_DIFF_SERV_DIVERSITY)));
                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());

                            body = z3.MkImplies(z3.MkAnd(Reachable[i, j], z3.MkEq(HOS[i], HOS[j]), z3.MkOr(Exprs)),
                                z3.MkEq(FlowDiv[i, j], z3.MkReal(SAME_OS_SAME_SERV_DIVERSITY)));
                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());
                        }
                }
                #endregion

                #region For All Hosts, Find the (OS) Usability
                {
                    for (i = 1; i <= nHost; i++)
                        for (j = 1; j <= nOS; j++)
                        {
                            BoolExpr body = z3.MkImplies(z3.MkEq(HOS[i], z3.MkInt(j)), z3.MkEq(HDivUsa[i], OSUsa[j]));
                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());
                        }
                }
                #endregion

                #endregion

                #region Resiliency and Usability Model

                #region Resiliency- Weighted Wum of Isolation and Diversity (for no transitivity)
                {
                    // If no reachability, then full resiliency
                    for (i = 1; i <= nHost; i++)
                        for (j = 1; j <= nHost; j++)
                        {
                            if (i == j)
                                continue;

                            BoolExpr body = z3.MkImplies(z3.MkNot(Reachable[i, j]),
                                z3.MkEq(FlowRes[i, j, 0], z3.MkReal(MAX_ISOLATION * ISOLATION_WEIGHT + MAX_DIVERSITY * DIVERSITY_WEIGHT)));
                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());
                        }

                    // When there is reachability?
                    for (i = 1; i <= nHost; i++)
                        for (j = 1; j <= nHost; j++)
                        {
                            if (i == j)
                                continue;

                            RealExpr Expr = (RealExpr)z3.MkAdd(z3.MkMul(FlowIso[i, j], z3.MkReal(ISOLATION_WEIGHT)),
                                z3.MkMul(FlowDiv[i, j], z3.MkReal(DIVERSITY_WEIGHT)));

                            BoolExpr body = z3.MkImplies(Reachable[i, j], z3.MkEq(FlowRes[i, j, 0], Expr));
                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());
                        }
                }
                #endregion

                #region Find the Resiliency at Different Transitivity Levels
                {
                    for (l = 1; l <= TRANSITIVITY_LEVEL; l++)
                    {
                        for (i = 1; i <= nHost; i++)
                            for (j = 1; j <= nHost; j++)
                            {
                                if (i == j)
                                    continue;

                                RealExpr[] Exprs = new RealExpr[nHost - 2];
                                int m = 0;
                                for (k = 1; k <= nHost; k++)
                                {
                                    if ((i == k) || (j == k))
                                        continue;

                                    Exprs[m++] = (RealExpr)z3.MkAdd(FlowRes[i, k, (l - 1)], FlowRes[k, j, 0]);   // In the below, the value is divided by 2
                                }

                                BoolExpr body = z3.MkEq(FlowRes[i, j, l], z3.MkDiv(z3.MkAdd(Exprs), z3.MkReal(2 * (nHost - 2))));

                                slvr.Assert(body);
                                twOut.WriteLine("{0}", body.ToString());
                            }
                    }
                }
                #endregion

                #region Find the Ultimate Resiliency Considering All Transitivity Levels
                {
                    for (i = 1; i <= nHost; i++)
                        for (j = 1; j <= nHost; j++)
                        {
                            if (i == j)
                                continue;

                            RealExpr[] Exprs = new RealExpr[TRANSITIVITY_LEVEL + 1];
                            for (l = 0; l <= TRANSITIVITY_LEVEL; l++)
                            {
                                Exprs[l] = (RealExpr)z3.MkMul(FlowRes[i, j, l], z3.MkReal(TRANSITIVITY_WEIGHT[l]));
                            }

                            BoolExpr body = z3.MkEq(FlowResUltimate[i, j], z3.MkAdd(Exprs));

                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());
                        }
                }
                #endregion

                #region Total Resiliency for a Host
                {
                    RealExpr[] TermsRes = new RealExpr[nHost - 1];

                    for (i = 1; i <= nHost; i++)
                    {
                        k = 0;

                        for (j = 1; j <= nHost; j++)
                        {
                            if (i == j)
                                continue;

                            TermsRes[k] = FlowResUltimate[j, i];
                            //TermsRes[k] = FlowRes[j, i, 2];

                            k++;
                        }

                        BoolExpr body = z3.MkEq(HRes[i], z3.MkAdd(TermsRes));
                        slvr.Assert(body);
                        twOut.WriteLine("{0}", body.ToString());
                    }
                }
                #endregion

                #region Usability for a Host- Weighted Sum of Isolation- and Diversity-Affected Usabilities
                {
                    for (i = 1; i <= nHost; i++)
                    {
                        RealExpr Expr = (RealExpr)z3.MkAdd(z3.MkMul(HIsoUsa[i], z3.MkReal(ISO_USABILITY_WEIGHT)),
                            z3.MkMul(HDivUsa[i], z3.MkReal(nHost - 1), z3.MkReal(DIV_USABILITY_WEIGHT)));

                        BoolExpr body = z3.MkEq(HResUsa[i], Expr);
                        slvr.Assert(body);
                        twOut.WriteLine("{0}", body.ToString());
                    }
                }
                #endregion

                #region Total Resiliency and Usability
                {
                    RealExpr[] TermsRes = new RealExpr[nHost];
                    RealExpr[] TermsUsa = new RealExpr[nHost];

                    k = 0;
                    for (i = 1; i <= nHost; i++)
                    {
                        TermsRes[k] = HRes[i];
                        TermsUsa[k] = HResUsa[i];

                        k++;
                    }

                    BoolExpr body;

                    body = z3.MkEq(Resiliency, z3.MkAdd(TermsRes));
                    slvr.Assert(body);
                    twOut.WriteLine("{0}", body.ToString());

                    body = z3.MkEq(Usability, z3.MkAdd(TermsUsa));
                    slvr.Assert(body);
                    twOut.WriteLine("{0}", body.ToString());
                }
                #endregion

                #endregion


                #region Cost Model

                #region Flow routes and dev in flow routes
                {
                    for (i = 1; i <= nHost; i++)
                    {
                        for (j = 1; j <= nHost; j++)
                        {
                            if (i == j)
                                continue;

                            nPath = 0;
                            getPath(i, j);

                            BoolExpr[] cond = new BoolExpr[nPath];

                            // DevInAllFlowRoutes -> DevInFlowRoute for all flow routes
                            if (nPath == 0)
                            {
                                slvr.Assert(z3.MkEq(DevInAllFlowRoutes[i, j], IZero));
                            }
                            else
                            {
                                for (k = 0; k < nPath; k++)
                                {
                                    cond[k] = z3.MkEq(DevInAllFlowRoutes[i, j], DevInFlowRoute[i, j, k + 1]);
                                }

                                BoolExpr body;
                                if (nPath > 1)
                                    body = z3.MkAnd(cond); //z3.MkImplies(pCond, z3.MkAnd(cond));
                                else
                                    body = cond[0]; //z3.MkImplies(pCond, cond[0]);

                                slvr.Assert(body);
                                twOut.WriteLine("{0}", body.ToString());
                            }
                        }
                    }
                }
                #endregion

                #region Flow isolation implies that required security device on flow routes
                //(but not the vice versa, as having a device does not mean isolation is activated)
                // If flowIso is not zero then flowIso and DevInAllFlowRoutes should be the same
                {
                    for (i = 1; i <= nHost; i++)
                        for (j = 1; j <= nHost; j++)
                        {
                            BoolExpr body = z3.MkImplies(z3.MkGt(FlowIsoMsr[i, j], IZero), z3.MkEq(DevInAllFlowRoutes[i, j], FlowIsoMsr[i, j]));

                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());
                        }
                }
                #endregion

                #region DevInAllFlowRoutes should be within zero to within the isolation devices
                {
                    for (i = 1; i <= nHost; i++)
                        for (j = 1; j <= nHost; j++)
                        {
                            BoolExpr body = z3.MkAnd(z3.MkGe(DevInAllFlowRoutes[i, j], IZero),
                                z3.MkLe(DevInAllFlowRoutes[i, j], z3.MkInt(nDev)));

                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());
                        }
                }
                #endregion

                #region For a link any of the case should be true: 0 (No device), 1 to NDev
                {
                    for (i = 1; i <= nLink; i++)
                    {
                        BoolExpr[] devs = new BoolExpr[nDev + 1];

                        for (j = 0; j <= nDev; j++)
                            devs[j] = DevInLink[i, j];

                        BoolExpr body = z3.MkOr(devs);
                        slvr.Assert(body);
                        twOut.WriteLine("{0}", body.ToString());
                    }
                }
                #endregion

                #region If DevInLink is zero (no device), then any other values are false (and vice-versa)
                {
                    for (i = 1; i <= nLink; i++)
                    {
                        BoolExpr[] devs = new BoolExpr[nDev];

                        for (j = 1; j <= nDev; j++)
                            devs[j - 1] = z3.MkNot(DevInLink[i, j]);

                        BoolExpr body = z3.MkImplies(DevInLink[i, 0], z3.MkAnd(devs));
                        slvr.Assert(body);
                        twOut.WriteLine("{0}", body.ToString());
                    }
                }
                #endregion

                #region For all link, if a device is placed on that link, the cost corresponds to the device
                {
                    for (i = 1; i <= nLink; i++)
                        for (j = 1; j <= nDev; j++)
                        {
                            // TODO: Will this casting work?
                            BoolExpr body = (BoolExpr)z3.MkITE(DevInLink[i, j], z3.MkEq(LinkDevCost[i, j], DevCost[j]), z3.MkEq(LinkDevCost[i, j], IZero));
                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());
                        }
                }
                #endregion

                #region Cost of OS intallations
                {
                    for (i = 1; i <= nHost; i++)
                        for (j = 1; j <= nOS; j++)
                        {
                            BoolExpr body = z3.MkImplies(z3.MkEq(HOS[i], z3.MkInt(j)), z3.MkEq(HOSCost[i], OSCost[j]));
                            slvr.Assert(body);
                            twOut.WriteLine("{0}", body.ToString());
                        }
                }
                #endregion

                #region Cost computation and corresponding constraints
                {
                    RealExpr[] termsDevCost = new RealExpr[nLink * nDev];

                    k = 0;
                    for (i = 1; i <= nLink; i++)
                    {
                        for (j = 1; j <= nDev; j++)
                        {
                            termsDevCost[k] = LinkDevCost[i, j];
                            k++;
                        }
                    }

                    RealExpr[] termsOSCost = new RealExpr[nHost];

                    k = 0;
                    for (i = 1; i <= nHost; i++)
                    {
                        termsOSCost[k] = HOSCost[i];
                        k++;
                    }

                    BoolExpr body = z3.MkEq(Cost, z3.MkAdd(z3.MkAdd(termsDevCost), z3.MkAdd(termsOSCost)));
                    slvr.Assert(body);
                    twOut.WriteLine("{0}", body.ToString());
                }
                #endregion

                #endregion

                #region Constraints on overall isolation, usability, and cost
                {
                    slvr.Assert(z3.MkGe(Resiliency, z3.MkReal(cRes)));
                    slvr.Assert(z3.MkGe(Usability, z3.MkReal(cUsa)));
                    slvr.Assert(z3.MkLe(Cost, z3.MkReal(cCost)));
                }
                #endregion


                //slvr.Push();
                #endregion


                #region output

                Enumerate();

                #endregion

                //Log.Close();
                //if (Log.isOpen())
                //    Console.WriteLine("Log is still open!");
            }
        }
        catch (Z3Exception ex)
        {
            Console.WriteLine("Z3 Managed Exception: " + ex.Message);
            Console.WriteLine("Stack trace: " + ex.StackTrace);
        }
        catch (Exception ex)
        {
            Console.WriteLine("Exception: " + ex.Message);
            Console.WriteLine("Stack trace: " + ex.StackTrace);
        }
    }

    // Enumerate the output 
    void Enumerate()
    {
        Model model = null;
        bSat = false;

        int i, j, k;
        int val;
        bool bVal;
        //int isolation, maxResiliency = 0;        

        twData.WriteLine("***********************************");
        twData.WriteLine("Problem with Hosts {0} and Routers {1}:...........", nHost, nRouter);
        twData.WriteLine("Resiliency, Usability, and Cost constraints are {0}, {1}, and {2}", res, usa, cost);

        #region Verification based on assumptions (Commented)
        {
            //Random rand = new Random();

            //int nAssump = numM;

            //String str;
            //Term[] p = new Term[nAssump];            
            //Term[] assumps = new Term[nAssump];

            //for (i = 0; i < nAssump; i++)
            //{
            //    str = String.Format("P{0}", i);
            //    p[i] = z3.MkConst(str, z3.BoolSort);

            //    k = rand.Next(numM, (numM + numC));
            //    slvr.Assert(z3.MkOr(p[0], z3.MkApp(Reachable, new Term[] { z3.MkNumeral(i, z3.IntSort), z3.MkNumeral(k, z3.IntSort) })));

            //    assumps[i] = z3.MkNot(p[i]);
            //}                                                                                                                                                        

            //Term proof;
            //Term[] cores = new Term[nAssump];

            //if (z3.CheckAssumptions(out model, assumps, out proof, out cores) == LBool.False)
            //{
            //    Console.WriteLine("We have no solution");
            //    Console.WriteLine("proof: {0}", proof);
            //    foreach (Term c in cores)
            //    {
            //        Console.WriteLine("Core: {0}", c);
            //    }
            //}
            //else
            //{
            //    Console.WriteLine("We have a solution");
            //    model.Display(Console.Out);
            //    z3.DisplayStatistics(Console.Out);
            //    model.Display(twOut);
            //}
        }
        #endregion

        #region Find solutions up to MAX_NUM_SOLUTION
        {
            int numSolution = 0;
            while (slvr.Check() == Status.SATISFIABLE)
            {
                bSat = true;

                model = slvr.Model;

                numSolution++;
                Console.WriteLine("{0}: We have a solution", numSolution);
                twOut.WriteLine("We have a solution");
                twData.WriteLine("{0}: We have a solution", numSolution);

                twOut.Write(model.ToString());
                twOut.WriteLine();

                //twData.WriteLine(slvr.Statistics);
                //twData.WriteLine();

                BoolExpr[] args = new BoolExpr[nLink * nDev];
                int nArgs = 0;

                twData.WriteLine("# Deployed security devices");
                k = 0;
                for (i = 1; i <= nLink; i++)
                {
                    for (j = 1; j <= nDev; j++)
                    {
                        bVal = Convert.ToBoolean(model.Eval(DevInLink[i, j]).ToString());
                        if (bVal)
                            args[nArgs++] = DevInLink[i, j];
                        else
                            args[nArgs++] = z3.MkNot(DevInLink[i, j]);

                        if (bVal)
                        {
                            twData.WriteLine("{0} {1}", i, j);
                            k++;
                        }
                    }
                }
                twData.WriteLine(k);
                twData.WriteLine();


                BoolExpr[] args2 = new BoolExpr[nHost * nHost];
                int nArgs2 = 0;

                twData.WriteLine("# Allowed traffic");
                k = 0;
                for (i = 1; i <= nHost; i++)
                {
                    for (j = 1; j <= nHost; j++)
                    {
                        val = Convert.ToInt32(model.Eval(FlowIsoMsr[i, j]).ToString());
                        args2[nArgs2++] = z3.MkEq(FlowIsoMsr[i, j], z3.MkInt(val));

                        if (Convert.ToInt32(model.Eval(IsoUsa[val]).ToString()) != 0)
                        {
                            twData.WriteLine("{0} {1} {2}", i, j, val);
                            k++;
                        }

                        //if(val > 0)
                        //    twData.WriteLine("Applied isolation: {0} {1} {2}", i, j, val);
                    }
                }
                twData.WriteLine(k);
                twData.WriteLine();

                twData.WriteLine("# Deployed operating systems");
                for (i = 1; i <= nHost; i++)
                {
                    twData.WriteLine("{0} {1}", i, model.Eval(HOS[i]).ToString());
                }
                twData.WriteLine();

                twData.WriteLine("# Deployed services");
                for (i = 1; i <= nHost; i++)
                {
                    twData.Write("{0}: ", i);
                    for (j = 1; j <= nServ; j++)
                    {
                        if (model.Eval(HServ[i, j]).IsTrue)
                        {
                            twData.Write("{0} ", j);
                        }
                        //twData.Write("{0} ", model.Eval(HServ[i, j]).ToString());
                    }
                    twData.WriteLine();
                }
                twData.WriteLine();

                twData.WriteLine("Resiliency: {0}", Convert.ToDouble(model.Eval(Resiliency).ToString()) / MAX_TOTAL_RESILIENCY);
                twData.WriteLine("Usability: {0}", Convert.ToDouble(model.Eval(Usability).ToString()) / MAX_TOTAL_USABILITY);
                twData.WriteLine("Cost: {0}", Convert.ToInt32(model.Eval(Cost).ToString()));

                model.Dispose();

                if (numSolution == MAX_NUM_SOLUTION)
                {

                    twData.WriteLine("***********************************");
                    twData.WriteLine();
                    break;
                }
                twData.WriteLine("..................................");

                slvr.Assert(z3.MkNot(z3.MkAnd(z3.MkAnd(args), z3.MkAnd(args2))));
                //slvr.Assert(z3.MkNot(z3.MkAnd(args2)));

                Console.WriteLine("Searching for another solution...");
                twData.WriteLine("Searching for another solution...");
            }
        }
        #endregion                

        if (!bSat)
        {
            twData.WriteLine(slvr.UnsatCore);

            Console.WriteLine("We have no solution");
            twOut.WriteLine("We have no solution");

            twData.WriteLine("We have no solution");
        }
        //else
        //    twData.WriteLine("The optimal isolation is {0}", maxResiliency * Convert.ToDouble(MAX_SLIDER_VAL) / MAX_TOTAL_RESILIENCY);

        //twData.WriteLine();
        //twData.Close();
    }


    // Main function
    static void Main(string[] args)
    {
        twOut = new StreamWriter("Output_R.txt", false);

        ConfigSynth config = new ConfigSynth();

        twData = new StreamWriter(String.Format("Data_R_{0}_{1}_{2}.txt", NUM_OF_HOST, NUM_OF_ROUTER, NUM_OF_LINK), true);

        Stopwatch stopWatch = new Stopwatch();
        stopWatch.Start();

        #region Program
        //config.SimulateInput();        

        config.Model();
        #endregion

        stopWatch.Stop();

        Console.WriteLine("Required time: {0}", stopWatch.Elapsed.TotalMilliseconds);
        twOut.WriteLine("Required time: {0}\n\n", stopWatch.Elapsed.TotalMilliseconds);

        TextWriter twStat = new StreamWriter("Statistics_R.txt", true);
        twStat.Write("Date and Time: {0} :: ", System.DateTime.Now);
        twStat.WriteLine("{0} {1} {2} {3} {4} {5} {6} {7} {8}", config.nDev, config.nHost, config.nRouter,
            config.nLink, res, usa, cost, config.bSat, stopWatch.Elapsed.TotalMilliseconds);
        twStat.Close();

        twData.Close();
        twOut.Close();
    }
};