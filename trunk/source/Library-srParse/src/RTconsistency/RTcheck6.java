package RTconsistency;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Iterator;
import java.util.Vector;

import pea.CDD;
import pea.PhaseEventAutomata;
import AdvancedPea.AdvPea;
import RTconsistency.RTcheck4.GI;
import pea.*;
import java.util.*;


/*
 * implizite D_0 Suche
 * 
 * 
 * 
 * 
 */
public class RTcheck6 {
	AdvPea[] pea;
	
	
	public RTcheck6( Vector<PhaseEventAutomata> peas )
	{
		int i;
		
		/*Collections.sort( peas, new Comparator<PhaseEventAutomata>()
				{ public int compare( PhaseEventAutomata p1, PhaseEventAutomata p2 )
					{ return p1.getPhases().length-p2.getPhases().length; } 
				} );*/
		
		
		int invcnt=0;
		for(i=0;i<peas.size();i++)
		{
			if( peas.get(i).getPhases().length==0 )
				invcnt++;
			else
				break;
		}
		pea=new AdvPea[peas.size()-invcnt];
		state=new int[peas.size()-invcnt];
		state[0]=-1;
		pea[0]=new AdvPea( peas.get(0) );
		//CDD inv=CDD.TRUE;
		for(i=1;i<peas.size();i++ )
		{
			if( i<invcnt )
			{
				//inv=inv.and( peas.get(i).getPhases()[0].getStateInvariant() );
				pea[0].inv_merge( new AdvPea( peas.get(i) ) );
			}
			else
			{
				pea[i-invcnt]=new AdvPea( peas.get(i) );
			 //	pea[i-invcnt].applyInvariantImplicit( inv );
				
			}
		}
		
		test1=new Test1( peas );
		
		int alen=0;
		
		
		
		{
			for( i=0;i<pea.length;i++)
			{
				if( pea[i].getActive(0)!=null )
					alen+=pea[i].getActive(0).length;
			}
			peanames=new String[alen];
			int j;
			int o=0;
			for(i=0;i<pea.length;i++)
			{
				if( pea[i].getActive(0)!=null )
				{
					for(j=0;j<pea[i].getActive(0).length;j++)
					{
						peanames[o]=pea[i].getName();
						o++;
					}
				}
			}
			test3=new Test3( alen );
		}
	}
	
	String[] peanames;
	Test1 test1;
	Test2 test2=new Test2();
	Test3 test3;
	
	public void printState( boolean reachable )
	{
		printState( reachable, state, true, false );
	}
	
	public void printState( boolean reachable, int[] state, boolean doTest, boolean isMinimized )
	{
		String s=new String();
		if( !reachable )
			s="unreachable ";
		
		CDD ci;
		if( state[0]>=0 )
		{
			s+=pea[0].getStateNames()[state[0]];
			ci=pea[0].getClockInvs()[state[0]];//CDD.TRUE;
		}
		else
			ci=CDD.TRUE;
		
		int alen=0;
		
		int[] act = new int[alen];
		int[] wait=new int[alen];
		int[] exa=new int[alen];
		int o=0;
		for(int j=1;j<pea.length;j++ )
		{
			if( state[j]<0 )
				continue;
			s+= "_X_" + pea[j].getStateNames()[state[j]];
			ci=ci.and( pea[j].getClockInvs()[state[j]] );
		}
		if( doTest )
		{
			test3.addDl( act, wait, exa );
			test1.addDl( s );
		}
		s+= " Clock Inv: "+ci;
		if( doTest )
			test2.addCInv( ci );
		//System.out.println( s );
		if( messageFile!=null )
        {
        	try {
				messageFile.write( s + "\r\n" );
				messageFile.flush();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
        	
        }
		else
			System.out.println( s );
		
		
		
		
	}
	
	public void check()
	{
			Reach1 reach=new Reach1( pea );
		
		if( findFirst() )
		{
			printState( /*reach.isReachable( state )*/ true );
			//printState( true, getMinDl(), false, true );
			while( findNext() )
			{
				printState( /*reach.isReachable( state )*/ true );
				//printState( true, getMinDl(), false, true );
			}
		}
		
		//test1.showCommon();
		//test2.printRes();
		test3.printCommon( peanames );
	}
	
	int[] state;

	int pos;
	
	
	private boolean instanceOfMinDeadlock( int[] state )
	{
		Iterator<int[]> it=minDeadlocks.iterator();
		
		mindl: while( it.hasNext() )
		{
			int[] s=it.next();
			
			for(int i=0;i<state.length;i++ )
			{
				if( s[i]>=0 && s[i]!=state[i] )
					continue mindl;
			}
			return true;
		}
		
		return false;
	}
	
	
	private boolean findFirst()
	{
		pos=0;
		int clk=0;
		for(int i=0;i<pea.length;i++ )
		{
			state[i]=0;
			CDD ci=pea[i].getClockInvs()[0];
			if( ci!=CDD.TRUE )
				clk++;
		}
		
		if( clk==0 )
		{
			return findNext();
		}
		else
		{
			if( !stateIsDl() )
				return findNext();
			else
				return true;
		}
	}
	
	
	private boolean findNext()
	{
		
		int clk=0;
		CDD inv=CDD.TRUE;
		boolean inc=true;
		
		while( true )
		{
			clk=0;
			inc=true;
			inv=CDD.TRUE;
			
			for(int i=pea.length-1;i>=0;--i)
			{
				if( inc )
				{
					if( (state[i]<pea[i].getStateInvs().length-1) )
					{
						state[i]++;
						inc=false;
					}
					else
					{
						state[i]=0;
					}
				}
				inv=pea[i].getStateInvs()[state[i]].and(inv);
				if( pea[i].getClockInvs()[state[i]]!=CDD.TRUE )
					clk++;
			}
			
			if( inc )
				return false; // kein weiterer zust gefunden
			
			if( clk>0 )
				if( inv==CDD.FALSE || instanceOfMinDeadlock( this.state ) || stateIsDl() )
					return true;
		}
		
		//return false; // sollte nicht erreciht werden
	}
	
	
	BufferedWriter messageFile=null;
    
    public void setMessageFile(String filename)
    {
    	try {
			//messageFile=new BufferedWriter(new FileWriter(filename,"UTF8"));
			messageFile = new BufferedWriter(new OutputStreamWriter( new FileOutputStream(filename), "UTF8")); 
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    	
    }
	
    private boolean stateIsDl()
    {
    	boolean res= stateIsDl( state );
    	if( res )
    	{
    		int[] minDL=getMinDl();
    		if( minDeadlocks!=null && minDeadlocks.add( minDL ) )
    			printState( true, minDL, false, true );
    	}
    	
    	return res;
    }
	
	/*
	 * true wenn einen DL geben könnte
	 */
	private boolean stateIsDl( int[] state )
	{
		CDD stateInv=CDD.TRUE;
		int i;
		Vector<GI>[] guards=new Vector[pea.length+1];
		
		guards[0]=new Vector<GI>();
		guards[0].add( new GI( CDD.TRUE, CDD.TRUE, 0, pea.length ) );
		guards[0].get(0).states[0]=-1;
		
		for(i=0;i<pea.length;i++ ) // für jeden pea
		{
			int k;
			guards[i+1]=new Vector<GI>();
			
			//for(k=0;k<pea[i].getGuards().length;k++ ) // jede phase im pea
			{
				k=state[i];
				
				if( k<0 )
				{
					for( int jj=0;jj<guards[i].size();jj++)
					{
						guards[i+1].add( guards[i].get(jj).clone() );
					}
					continue;
				}
				
				int j;
				stateInv=stateInv.and( pea[i].getStateInvs()[k] );
				
				if( stateInv==CDD.FALSE )
				{
					return false; // zust ex nicht
				}
				
				for( int n=0;n<pea[i].getGuards()[k].length;n++ ) // jede ausgehende trans
				{
					CDD inv, g;
					g=pea[i].getGuards()[k][n].unprime();
					if( g==CDD.FALSE )
						continue;
					
					
					CDD[] disj=pea[i].getUntimedDisjuncts( g );
					inv=pea[i].getStateInvs()[n];
					for(int ii=0;ii<disj.length;ii++ ) // für jedes disjunktionsglied
					{
						for(j=0;j<guards[i].size();j++) // für jedes bisherige prefix
						{
							GI gi=guards[i].get(j).and( disj[ii], inv );
							if( !gi.isFalse() )
							{
								gi.states[i]=n;
								guards[i+1].add( gi );
							}
						}
					}
				}
				
				if( guards[i+1].size()==0 )
				{
					//System.out.println( "DL found in: " );
					//printState();
					return true;
				}
			}
		}
		
		if( guards[guards.length-1].size()>0 )
		{
			int delcnt=0;
			boolean del;
			for( int k=0;k<guards[guards.length-1].size();k++ )
			{
				del=true;
				for(i=0;i<guards[guards.length-1].get(0).states.length;i++ )
				{
					if( guards[guards.length-1].get(0).states[i]!=state[i] )
					{
						del=false;
						break;
					}
				}
				
				if( !del )
				{
					CDD in=guards[guards.length-1].get(k).inv;
					CDD g=guards[guards.length-1].get(k).guard.unprime();
					CDD a=in.and(g);
					if( a==CDD.FALSE )
					{
						del=true;
					}
				}
				
				if( del )
					delcnt++;
			}
			
			if( (guards[guards.length-1].size()-delcnt)<=0 )
			{
				return true;
			}
		}
			
		return false;
	}
	
	
	
	
	
	class GI
	{
		CDD guard;
		CDD inv;
		int selfloops;
		int[] states;
		
		public GI( CDD guard, CDD state_inv, int selfloops, int len )
		{
			this.guard=guard;
			this.inv=state_inv;
			this.selfloops=selfloops;
			states=new int[len];
		}
		
		public GI( CDD guard, CDD state_inv, int selfloops, int[] states )
		{
			this( guard, state_inv, 0, states.length );
			System.arraycopy( this.states, 0, states, 0, states.length );
		}
		
		public GI( CDD guard, CDD state_inv, int len )
		{
			this( guard, state_inv, 0, len );
		}
		
		public GI clone()
		{
			return new GI( guard, inv, selfloops, states.length );
		}
		
		
		public GI and( CDD guard, CDD inv )
		{
			return new GI(this.guard.and( guard ), this.inv.and( inv ), selfloops, states );
		}
		
		public boolean isFalse()
		{
			CDD g=guard.and(inv);
			return ( (guard==CDD.FALSE) || (inv==CDD.FALSE) || (g==CDD.FALSE) );
		}
		
		public String toString()
		{
			String state=new String();
			state+=": "+pea[0].getStateNames()[states[0]];
			for(int j=1;j<pea.length;j++ )
			{
				state+= "_X_" + pea[j].getStateNames()[states[j]];
			}
			state+= " dlCheck: " + inv.toString();
			return state;
		}
	}





	public int[] getState() {
		return state;
	}

	public void setState(int[] state) {
		this.state = state;
	}

	
	private boolean check_2_reachability( int[] states )
	{
		
		int i;
		
		for(i=0;i<states.length-1;i++)
		{
			for( int j=i+1;j<states.length;j++)
			{
				if( !is_2_reach( i, states[i], j, states[j] ) )
				{
					return false;
				}
			}
		}
		
		return true;
	}
	
	
	private boolean is_2_reach( int pea1, int phase1, int pea2, int phase2 )
	{
		
		// todo: ordentlich implementieren
		PhaseEventAutomata pp=pea[pea1].getPea().parallel( pea[pea2].getPea() );
		
		int i;
		String name=pea[pea1].getStateNames()[phase1]+"_X_"+pea[pea2].getStateNames()[phase2];
		for(i=0;i<pp.getPhases().length;i++)
		{
			if( pp.getPhases()[i].getName().compareTo( name )==0 )
			{
				return true;
			}
		}
		
		return false;
	}
	
	private int[] getMinDl()
	{
		// assert( state is deadlock )
		int[] res=new int[ state.length ];
		System.arraycopy( state, 0, res, 0, state.length );
		
		for( int i=0;i<state.length;i++ )
		{
			res[i]=-1;
			if( !stateIsDl( res ) )
			{
				res[i]=state[i];
			}
		}

		
		if( minDeadlocks!=null )
			if( minDeadlocks.add( res ) )
			{
				printState( true, res, false, true );
			}
		return res;
	}
	
	
	private Set<int[]> minDeadlocks=null;


	public Set<int[]> getMinDeadlocks() {
		return minDeadlocks;
	}

	public void setMinDeadlocks(Set<int[]> minDeadlocks) {
		this.minDeadlocks = minDeadlocks;
	}
}
