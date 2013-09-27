package RTconsistency;

import AdvancedPea.*;
import pea.*;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.*;



/*
 * RTcheck4
 * 
 * Sehr einfache Symbolische Suche, findet alle
 * 
 */

public class RTcheck4 {
	AdvPea[] pea;
	
	public RTcheck4( Vector<PhaseEventAutomata> peas )
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
		pea[0]=new AdvPea( peas.get(0) );
		for(i=1;i<peas.size();i++ )
		{
			if( i<invcnt )
			{
				pea[0].inv_merge( new AdvPea( peas.get(i) ) );
			}
			else
				pea[i-invcnt]=new AdvPea( peas.get(i) );
		}
	}
	
	
	
	/*
	 * true wenn es eine Transition gibt, die nicht von einer clock abhängt
	 */
	private boolean untimedExists( int[] states, int startIndex, Vector<CDD> guards, Vector<CDD> invs )
	{
		Vector<CDD> guards_new;
		Vector<CDD> invs_new;
		
		if( startIndex>=states.length )
		{
			return (guards.size()>0);
		}
		
		if( guards==null )
		{
			guards=new Vector<CDD>();
			guards.add( CDD.TRUE );
			invs=new Vector<CDD>();
			invs.add( CDD.TRUE );
		}
		
		CDD[] disj;
		
		//for(int i=0;i<pea.length;i++ )
		{
			guards_new=new Vector<CDD>();
			invs_new=new Vector<CDD>();
			for( int j=0;j<pea[startIndex].getGuards().length;j++)
			{
				if( states[startIndex]==j ) // skip selfloops
					continue;
				
				disj=pea[startIndex].getUntimedDisjuncts( pea[startIndex].getGuards()[states[startIndex]][j] );
				
				if( disj.length==0 )
					continue;
				
				for(int k=0;k<guards.size();k++)
				{
					CDD s=invs.get(k).and( pea[startIndex].getStateInvs()[j] );
					if( s!=CDD.FALSE )
					{
						for( int ii=0;ii<disj.length;ii++ )
						{
							CDD t=guards.get(k).and(disj[ii]);
							
							if( t!=CDD.FALSE )
							{
								guards_new.add(t);
								invs_new.add(s);
							}
						}
					}
				}
			}
			
			if( guards_new.size()==0 )
				return true;
			
			return untimedExists( states, startIndex+1, guards_new, invs_new );
			//if( untimedExists( states, startIndex+1, guards_new ) )
				//return true;
		}
		
		//return false;
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
		
		public void and( CDD guard, CDD inv )
		{
			this.guard=this.guard.and( guard );
			this.inv=this.inv.and( inv );
		} 
		
		
		public GI and2( CDD guard, CDD inv )
		{
			return new GI(this.guard.and( guard ), this.inv.and( inv ), selfloops, states );
		}
		
		public boolean isFalse()
		{
			return ( (guard==CDD.FALSE) || (inv==CDD.FALSE) );
		}
		
		public String toString()
		{
			String state=new String();
			state+=": "+pea[0].getStateNames()[states[0]];
			for(int j=1;j<pea.length;j++ )
			{
				state+= "_X_" + pea[j].getStateNames()[states[j]];
			}
			state+= " s: " + inv.toString();
			return state;
		}
	}
	
	
	
	/*
	 * true wenn es eine Transition gibt, die nicht von einer clock abhängt
	 */
	private boolean untimedExists_GI( int[] states, int startIndex, Vector<GI> guards, boolean skipTimed )
	{
		Vector<GI> guards_new;
		
		if( startIndex>=states.length )
		{
			/*if(guards.size()>0)
			{
				for(int i=0;i<guards.size();i++ )
					System.out.println( guards.get(i) );
			}*/
			
			
			return ( (guards.size()>0) );
		}
		
		if( guards==null )
		{
			guards=new Vector<GI>();
			guards.add( new GI(CDD.TRUE, CDD.TRUE, 0, states.length) );
		}
	
		CDD[] disj;

		guards_new=new Vector<GI>();
		for( int j=0;j<pea[startIndex].getGuards().length;j++)
		{
			CDD tmp=pea[startIndex].getGuards()[states[startIndex]][j];
			disj=pea[startIndex].getUntimedDisjuncts( tmp );
			
			if( disj.length==0 )
			{
				continue;
			}
			
			for(int k=0;k<guards.size();k++)
			{
				GI g=guards.get(k);
				for( int ii=0;ii<disj.length;ii++ )
				{
					GI t=g.and2( disj[ii], pea[startIndex].getStateInvs()[j] );
					t.states[startIndex]=j;
					
					if( !t.isFalse() )
					{
						if( j==states[startIndex] )
							t.selfloops++;
						
						guards_new.add(t);
					}
				}
			}
		}
		
		if( guards_new.size()==0 )
			return false;
		
		return untimedExists_GI( states, startIndex+1, guards_new, skipTimed );
	}
	
	
	int[] dlState;
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
	
	/*
	 * true - wenn es eine Location in parallelautomat geben könnte, die diese Location enthält
	 */
	//private boolean stateExists( int excludeIdx, int excludeStateIndex, int startIndex, CDD cdd )
    private boolean stateExists( int startIndex, CDD cdd )
	{
		//int idx;
		int i;
		boolean res;
		
		if( startIndex>=pea.length )
		{
			if( untimedExists_GI( dlState, 0, null, true ) )
			{
				String state= "Symbolic search detected lDl";
				if( !check_2_reachability( dlState ) )
				{
					state+=" (2-unreachable)";
				}
				
				state+=": "+pea[0].getStateNames()[dlState[0]];
				for(int j=1;j<pea.length;j++ )
				{
					state+= "_X_" + pea[j].getStateNames()[dlState[j]];
				}
				System.out.println( "dl state exists: " + state );
				
				if( messageFile!=null )
		        {
		        	try {
						messageFile.write( state + "\r\n" );
						messageFile.flush();
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
		        	
		        }
				
			//	return true; // zu true ändern um jeweils nur 1. zu erhalten
			}
			return false;//untimedExists( dlState, 0, null, null );
		}
		
		for(i=0;i<pea[startIndex].getPhaseCount();i++ )
		{
			CDD t;
			/*if( excludeIdx==startIndex )
				idx=excludeStateIndex;
			else
				idx=i;*/
			
			if( cdd==null )
				t=pea[startIndex].getStateInvs()[i];
			else
				t=cdd.and( pea[startIndex].getStateInvs()[i] );
			
			if( t==CDD.FALSE )
			{
				return false;
			}
			
			dlState[startIndex]=i;
			res= stateExists( startIndex+1, t );
			
			if( res )
				return true;	
		}
		return false;
	}
	
	
	public Vector<String> getDl( )
	{
		int i;
		Vector<String>res =new Vector<String>();
		
		dlState=new int[pea.length];
		
		//for(i=0;i<pea[index].getTimed().length;i++)
		{
			for(int j=0;j<pea.length;j++)
			{
				dlState[j]=0;
			}
			
			if( stateExists( 0, null) /*&& stateExists( index, pea[index].getTimed()[i], 0, null, null)*/ )
			{
				/*String state=pea[0].getStateNames()[dlState[0]];
				for(int j=1;j<pea.length;j++ )
				{
					state+= "_" + pea[j].getStateNames()[dlState[j]];
				}
				System.out.println( "dl state exists: " + state );*/
			}
		}
		
		return res;
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
	
}
