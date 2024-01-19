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
    
    void displayBasicBlk() {
 	   for(BiLink p =f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
 		   BasicBlk v=(BasicBlk)p.elem();
 		   System.out.println("");
 		   System.out.println("-------------------------------------------");
 		   System.out.println(v.label()+". id:"+v.id);
 		   for(BiLink bl=v.instrList().first();!bl.atEnd();bl=bl.next()){
 			   LirNode node=(LirNode)bl.elem();
 			   System.out.println(node);
 		   }
 	   }
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
    	
    	BiLink latest = null;
    	BiLink p1 = q.next();
    	LirNode m = (LirNode)p1.elem();
    	int same_index_num = checkIndexNum(node.kid(0), m.kid(0), exprIndexNum);
    	
    	for(BiLink p2=q.next();!p2.atEnd();p2=p2.next() ) {
    		
    		LirNode n = (LirNode)p2.elem();
    		ArrayList<LirNode> nvars = new ArrayList<LirNode>();
    		collectVars(nvars, n);
    		
    		if (nvars.contains(node.kid(0))) {
    			return false;
    		}
    		
    		if (!(isStore(n) && sameAddr(n,Addr) && sameIndexNum(n.kid(0)))) {
    			
    			continue;
    		}
    		
    		int same = checkIndexNum(node.kid(0), n.kid(0), exprIndexNum);
    		
    		if ( same > same_index_num ) {
    			latest = p2;
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
    	
    	
		for(int i=bVecInOrderOfRPost.length - 1;i > 0; i--) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
				LirNode node = (LirNode)p.elem();
				
				
				if(!isStore(node)) {
					continue;
				}
				
				LirNode addr = getAddr(node.kid(0));
				ArrayList<LirNode> vars = new ArrayList<LirNode>();
				collectVars(vars,node.kid(0));
				
				if(p!=blk.instrList().last()){
					
					if(localCM(node,addr,vars,blk,p)) {
						
						System.out.println("MDGSA=true");
						p.unlink();
					}
					
				}
				
			}
			
		}
		
	}

    void invoke() {
    	localCodeMotion();
    	displayBasicBlk();
     
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

    
    dfst=(DFST)f.require(DFST.analyzer);
    initialized = new boolean[f.flowGraph().idBound()];
    memArray = new boolean[f.flowGraph().idBound()];
    
    bVecInOrderOfRPost = dfst.blkVectorByRPost();

   
    
   
    invoke();
    alias.annul();

    
    f.flowGraph().touch();
    return(true);
    }
  
}

