/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
/*
the case where a query reaches uneffective traces of propagated queries is problem.
*/


package coins.ssa;

import java.util.ArrayList;

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.ana.DFST;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;

public class MDGSA implements LocalTransformer {
    private boolean debugFlag;

    public boolean doIt(Data data, ImList args) { return true; }
    public String name() { return "MDGSA"; }
    public String subject() {
	return "Optimizatin with efficient question propagation.";
    }

   
    public BasicBlk[] bVecInOrderOfRPost;
    int exprIndexNum;
    int idBound;

    private int mode;

    private Util util;
    private String tmpSymName="_mdgsa";
    public static final int THR=SsaEnvironment.OptThr;
    /** The threshold of debug print **/
    public static final int THR2=SsaEnvironment.AllThr;
    private SsaEnvironment env;
    private SsaSymTab sstab;
    private Function f;
    
    
    private DFST dfst;
    
    boolean initialized[];

   
   
    MemoryAliasAnalyze alias;
    /*    private Hashtable memArgs;*/
    boolean[] memArray;

    /**
     * Constructor
     * @param e The environment of the SSA module
     * @param tab The symbol tabel of the SSA module
     * @param function The current function
     * @param m The current mode
     **/
    public MDGSA(SsaEnvironment env, SsaSymTab sstab){
    	this.env = env;
    	this.sstab = sstab;
      
    }
    public boolean isStore(LirNode node) {
    	return(node.opCode == Op.SET && node.kid(0).opCode == Op.MEM );
    	
    }
    
    public boolean isLoad(LirNode node) {
    	return(node.opCode == Op.SET && node.kid(1).opCode == Op.MEM );
    	
    }
    
   
    public int getIndexNum(LirNode exp) {
    	
		int num = 0;
		LirNode kid = exp.kid(0);
		
		while(kid.opCode == Op.ADD ) {
			num++;
			kid = kid.kid(0);
		}
		
		return num;
    	
    }
    
    LirNode getIndex(LirNode mem) {
		if(mem.kid(0).opCode!=Op.ADD) {
			return null;
		}
		return mem.kid(0).kid(1);
	}
    
    public boolean sameIndexNum(LirNode exp) {
    	int indexNum = getIndexNum(exp);
    	return (indexNum == exprIndexNum);
    }
    
    int checkIndexNum(LirNode exp1, LirNode exp2, int index){
		if(exp2.opCode==Op.SET) {
			return checkIndexNum(exp1.kid(1).kid(0),exp2.kid(1).kid(0),index);
		}
		else if(exp2.opCode==Op.MEM) {
			return checkIndexNum(exp1.kid(0),exp2.kid(0),index);
		}
		LirNode expKid = exp1;
		LirNode exprKid = exp2;
		while(expKid.opCode==Op.ADD){
			if(exprKid.equals(expKid)) {
				break;
			}
			expKid = expKid.kid(0);
			exprKid = exprKid.kid(0);
			index--;
		}
		return index;
	}
    
    LirNode getAddr(LirNode exp){
    	if(exp.nKids()==0) return exp;
		if(exp.kid(0).nKids()==0) return exp.kid(0);
		else return getAddr(exp.kid(0));
	}
    
    boolean sameAddr(LirNode node, LirNode addr) {
    	if(isStore(node)) {
    		return ( addr.equals(getAddr(node.kid(0))) );
    	}
    	return false;
    }
    
    public void collectVars(ArrayList<LirNode> vars, LirNode exp){
		for(int i=0;i<exp.nKids();i++){
			if(exp.kid(i).opCode==Op.REG) vars.add(exp.kid(i).makeCopy(env.lir));
			else if(exp.kid(i).nKids()>0) collectVars(vars,exp.kid(i));
		}
	}
    
    boolean localCM(LirNode node, LirNode Addr, ArrayList<LirNode> vars, BasicBlk blk, BiLink q) {
        exprIndexNum = getIndexNum(node.kid(0));
    	int same_index_num = 0;
    	
    	BiLink latest = null;
    	
    	//System.out.println(node.kid(0));
    	
    	for(BiLink p=q.next();!p.atEnd();p=p.next() ) {
    		
    		LirNode n = (LirNode)p.elem();
    		ArrayList<LirNode> nvars = new ArrayList<LirNode>();
    		collectVars(nvars, n);
    		if(isStore(n)) {
    		//System.out.println("n" + n);
    		//System.out.println("Addr" + Addr);
    		//System.out.println(getIndexNum(n.kid(0)));
    		//System.out.println("sameAddr" + sameAddr(n,Addr));
    		//System.out.println(n);
    		//System.out.println("CM" + n.kid(1));
    		
    		}
    		
    		
    		if (nvars.contains(node.kid(0))) {
    			return false;
    		}
    		
    		if (!(isStore(n) && sameAddr(n,Addr) && sameIndexNum(n.kid(0)))) {
    			
    			continue;
    		}
    		
    		int same = checkIndexNum(node.kid(0), n.kid(0), exprIndexNum);
    		//System.out.println(same);
    		if ( same < same_index_num ) {
    			latest = p;
    			latest.addBefore(node.makeCopy(env.lir));
    			return true;
    		} else {
    			same_index_num = same;
    		}
    		
    		
    	}
    	//System.out.println("");
    	return false;
    }
    void localCodeMotion(){
    	
    	//System.out.println(bVecInOrderOfRPost.length);
		for(int i=bVecInOrderOfRPost.length - 1;i > 0; i--) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			//System.out.println("blk" + blk.label());
			//System.out.println("");
			for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
				LirNode node = (LirNode)p.elem();
				//System.out.println("node;" + node);
				
				if(!isStore(node)) {
					continue;
				}
				
				LirNode addr = getAddr(node.kid(0));
				ArrayList<LirNode> vars = new ArrayList<LirNode>();
				collectVars(vars,node.kid(0));
				//System.out.println(getIndexNum(node.kid(0)) + ":");
				//System.out.println("node:" + node.kid(0));
				//System.out.println(addr);
				//System.out.println("");
				if(p!=blk.instrList().last()){
					//System.out.println("localCM:" + localCM(node,addr,vars,blk,p));
					if(localCM(node,addr,vars,blk,p)) {
						System.out.println("MDGSA=true");
						p.unlink();
					}
					//System.out.println("");
				}
				
				//System.out.println("");
			}
			
			//System.out.println("");
		}
		
		//System.out.println("");
	}

    void invoke() {

     
    }

    

  /**
   * Do optimize using Efficient Question Propagation.
   * @param f The current function
   **/
    public boolean doIt(Function function,ImList args) {
      //

      //long startTime = System.currentTimeMillis();

      //
    f = function;
    util=new Util(env,f);
    env.println("****************** doing MDGSA to "+
    f.symbol.name,SsaEnvironment.MinThr);
    alias=new MemoryAliasAnalyze(env,f);

    // 1/3 
    dfst=(DFST)f.require(DFST.analyzer);
   

   
    initialized = new boolean[f.flowGraph().idBound()];

    // Sort the arguments of all phi instructions
   
    /*    memArgs = new Hashtable();*/
    memArray = new boolean[f.flowGraph().idBound()];
    
    bVecInOrderOfRPost = dfst.blkVectorByRPost();
    localCodeMotion();
    
    BiLink b = null;
    int count = 0;
    for(int i=bVecInOrderOfRPost.length - 1;i > 0; i--){
    	BasicBlk blk = bVecInOrderOfRPost[i];
        //System.out.println("blked" + v.label() );
        //System.out.println("");
	for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
		
		ArrayList<LirNode> vars = new ArrayList<LirNode>();
	    LirNode node=(LirNode)p.elem();
	    
	    if ( isStore(node) ) {
	    
	    
	    
	    //System.out.println(getIndexNum(node.kid(0)));
	    //System.out.println("nodeed:" + node.kid(0));
	    //System.out.println("");
	   
	    }
	   
	    }
	    //System.out.println(count);
	    //System.out.println("");
	    
	}
    //System.out.println("");
    


   
    invoke();
    alias.annul();

    
    f.flowGraph().touch();
    return(true);
    }
  
}

