package RTconsistency;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;

import pea.*;
import AdvancedPea.AdvPea;
import RTconsistency.RTcheck6.GI;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.lang.Math;


/*
 * Implizite D_1 Suche als Breitensuche 
 * 
 * Prüft die graphbasierte Erreichbarkeit von Deadlocks in D_0
 * 
 * Eingabe: Lister minimaler Deadlocks(wird von RTcheck6 ) berechnet
 * 
 * somit werden nur erreichbare Dl gefunden
 * 
 */
public class RTcheck8 {
	
	AdvPea[] pea;
	//int[] state;
	
	public RTcheck8( Vector<PhaseEventAutomata> peas )
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
		//state=new int[peas.size()-invcnt];
		//state[0]=-1;
		pea[0]=new AdvPea( peas.get(0) );
		for(i=1;i<peas.size();i++ )
		{
			if( i<invcnt )
			{
				pea[0].inv_merge( new AdvPea( peas.get(i) ) );
			}
			else
			{
				pea[i-invcnt]=new AdvPea( peas.get(i) );
			}
		}
		
		//test1=new Test1( peas );
		
		/*int alen=0;
		
		for( i=0;i<pea.length;i++)
		{
			alen+=pea[i].getActive(0).length;
		}
		peanames=new String[alen];
		int j;
		int o=0;
		for(i=0;i<pea.length;i++)
		{
			for(j=0;j<pea[i].getActive(0).length;j++)
			{
				peanames[o]=pea[i].getName();
				o++;
			}
		}
		test3=new Test3( alen );*/
	}
	
	Vector<int[]> initials;
	int[] deleted;
	int[] explored;
	int[] nextstates;
	int[] bitoffs;
	//int[] deadlocks;
	public Set<int[]> minDeadlocks=new HashSet<int[]>();
	int size;
	
	
	public void check()
	{
		findInitials();
		int[] state;
		
		if( initials.size()<=0 )
		{
			return;
		}
		
		// get needed size for bitsfields
		size=pea[0].getPhaseCount();
		int i;
		bitoffs=new int[pea.length];
		bitoffs[0]=1;
		for( i=1;i<pea.length;i++ )
		{
			bitoffs[i]=size;
			size*=pea[i].getPhaseCount();
		}
		
		bitoffs[bitoffs.length-1]=size;
		//size/32+1
		int num=(int)Math.ceil( ((double)size)/32.0 )+1;
		num=size;
		deleted=new int[num];
		explored=new int[num];
		nextstates=new int[num];
		//deadlocks=new int[num];
		
		// initials prüfen
		for( i=0;i<initials.size();i++ )
		{
			state=initials.get(i);
			
			int idx,msk;
			idx=getBitNum( state );
			msk=1<<(idx%32);
			idx/=32;
			//if( ( explored[idx] & msk ) == 1 )
				//continue;
			
			nextstates[idx] |= msk;
			
			/*if( stateIsDl( state ) )
			{
				printState( true, state, false, false );
			}
			searchNext( state );*/
		}
		
		
		boolean hasopen=true;
		while( hasopen )
		{
			hasopen=false;
			
			for(i=0;i<nextstates.length;i++)
			{
				if( nextstates[i]!=0 )
				{
					hasopen=true;
					int n,t;
					n=0;
					t=nextstates[i];
					while( (t & 1) == 0 )
					{
						t=t>>1;
						n++;
					}
					nextstates[i]^=1<<n; // gefundene loc aus neu liste entfernen
					explored[i]  |=1<<n; // und als untersucht markieren
					state=getStateFromIdxMsk( i,n );
					
					if( state!=null )
					{
						if( instanceOfMinDeadlock( state ) )
						{
							printState( true, state, false, false );
						}
						/*else
						{
							if( stateIsDl( state ) )
							{
								int[] min=getMinDl( state );
								printState( true, state, false, false );
								
								if( minDeadlocks.add( min ) )
									printState( true, min, false, true );
							}
						}*/
					
						searchNext( state );
					}
				}
			}
		}
	}
	
	
	public boolean addMinDeadlock( int[] state )
	{
		return minDeadlocks.add( state );
	}
	
	
	private int[] getMinDl( int[] state )
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

		return res;
	}
	
	private int[] getMinDel( int[] state )
	{
		// assert( state is deleted )
		int[] res=new int[ state.length ];
		System.arraycopy( state, 0, res, 0, state.length );
		
		for( int i=0;i<state.length;i++ )
		{
			res[i]=-1;
			if( getStateInv( res )!=CDD.FALSE )
			{
				res[i]=state[i];
			}
		}

		return res;
	}
	
	private void searchNext( int[] state )
	{
		// assert( location existiert und ist erreichbar )
		//nextstates=new int[(size/32)+1];
		int[] succ;
		int idx, mask;
		
		
		succ=findNext( state, new int[pea.length] );
		while( succ!=null )
		{
			idx=getBitNum( succ );
			//System.out.print( "Add to List: ("+idx+") " );
			//printState( true, succ, false, false );
			
			mask=1<<(idx%32);
			idx=idx/32;
			nextstates[idx]|=mask;
			
			/*if( stateIsDl( state ) )
			{
				printState( true, state, false, false );
			}*/
			
			succ=findNext( state, succ );
		}
	}
		
	
	private int[] getStateFromIdxMsk( int idx, int mask )
	{
		int[] res=new int[pea.length];
		int i;
		
		int v=idx*32+mask;
		
		for(i=pea.length-1;i>=0;i--)
		{
			res[i]=v/bitoffs[i];
			v=v%bitoffs[i];
		}
		
		return res;
	}
	
	private CDD getClockInv( int[] state )
	{
		CDD inv=CDD.TRUE;
		int i;
		
		for( i=0;i<pea.length;i++ )
		{
			inv=inv.and( pea[i].getClockInvs()[state[i]] );
		}
		
		return inv;
	}
	
	private CDD getStateInv( int[] state )
	{
		CDD inv=CDD.TRUE;
		int i;
		
		for( i=0;i<pea.length;i++ )
		{
			inv=inv.and( pea[i].getStateInvs()[state[i]] );
		}
		
		return inv;
	}
	
	/*
	 * gibt die nächste mit this.state vebundene und unbekannte location zurück
	 *  
	 * Es werden alle Locations auf bekanntheit udn verbundenheit mit this.state überprüft
	 * 
	 * todo: besser machen
	 */
	private int[] findNext( int[] state, int[] lastSucc )
	{
		int j;
		//int clk=0;
		CDD inv=CDD.TRUE;
		CDD guard=CDD.TRUE;
		boolean inc=true;
		
		while( true )
		{
			//clk=0;
			inc=true;
			inv=CDD.TRUE;
			guard=CDD.TRUE;
			
			for(int i=pea.length-1;i>=0;--i)
			{
				if( inc )
				{
					/*if( (lastSucc[i]<pea[i].getStateInvs().length-1) )
					{
						lastSucc[i]++;
						inc=false;
					}
					else
					{
						state[i]=0;
					}*/
					for( int k=lastSucc[i]+1;k<pea[i].getStateInvs().length;k++ )
					{
						if( pea[i].getGuards()[state[i]][k]!=CDD.FALSE )
						{
							lastSucc[i]=k;
							inc=false;
							break;
						}
					}
					if( inc )
					{
						for( int k=0;k<pea[i].getStateInvs().length;k++ )
						{
							if( pea[i].getGuards()[state[i]][k]!=CDD.FALSE )
							{
								lastSucc[i]=k;
								break;
							}
						}
					}
				}
				//inv=pea[i].getStateInvs()[lastSucc[i]].and(inv);
				//guard=guard.and( pea[i].getGuards()[state[i]][lastSucc[i]] );
			}
			
			if( inc )
				return null; // kein weiterer zust gefunden
			
			if( isOpen( lastSucc ) )
			{
				GI g=getGI( state, lastSucc );
				inv=g.inv;
				guard=g.guard;
				
				if( inv==CDD.FALSE )
				{
					int idx=getBitNum( lastSucc );
					int mask=1<<(idx%32);
					idx=idx/32;
					deleted[idx]|=mask;
					
				}
				else
				{
					if( guard!=CDD.FALSE && inv.and( guard )!=CDD.FALSE /*&& isConnected( this.state, state )*/ )
						return lastSucc;
				}
			}
		}
		
	}
	
	
	private GI getGI( int[] state, int[] succ )
	{
		CDD inv=CDD.TRUE;
		CDD gu=CDD.TRUE;
		
		for(int i=0;i<state.length;i++ )
		{
			inv=pea[i].getStateInvs()[succ[i]].and(inv);
			gu=gu.and( pea[i].getGuards()[state[i]][succ[i]] );
		}
		
		GI g=new GI( inv, gu, 0);
		return g;
	}
	
	private boolean isConnected( int[] stateStart, int[] state2 )
	{
		CDD guard=CDD.TRUE;
		CDD inv=CDD.TRUE;
		int i;
		
		for( i=0;i<pea.length;i++ )
		{
			guard=guard.and( pea[i].getGuards()[stateStart[i]][state2[i]] );
			inv=inv.and( pea[i].getStateInvs()[state2[i]] );
			
			if( guard==CDD.FALSE || inv==CDD.FALSE )
				return false;
		}
		
		return guard.and( inv )!=CDD.FALSE;
	}
	
	
	/*
	 * true wenn state nicht bekannt ist
	 * 
	 */
	private boolean isOpen( int[] state )
	{
		int idx, mask;
		idx=getBitNum( state );
		mask=1<<(idx%32);
		idx=idx/32;
		
		return ( ( ( explored[idx] & mask ) == 0 ) && ( ( nextstates[idx] & mask ) == 0 ) && ( ( deleted[idx] & mask ) == 0 ) );
	}
	
	
	
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
	
	
	/*private boolean stateIsDl()
    {
    	return stateIsDl( state );
    }*/
	
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
		
		//bis dahin baut das den Parallelautomaten auf
		//ab hier deadlockspezifisch
		
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
	
	
	
	
	
	
	private int getBitNum( int[] state )
	{
		int res=state[0];
		int i;
		
		for(i=1;i<pea.length;i++)
		{
			res+=state[i]*bitoffs[i];
		}
		
		return res;
	}
	
	private void findInitials()
	{
		initials=new Vector<int[]>();
		int i,j,k;
		
		for( j=0;j<pea[0].getInitial().length;j++ )
		{
			int[] state=new int[pea.length];
			state[0]=pea[0].getInitial()[j];
			initials.add( state );
		}
		
		for(i=1;i<pea.length;i++ )
		{
			int[] state;
			int[] s;
			Vector<int[]> init=new Vector<int[]>();
			for( j=0;j<pea[i].getInitial().length;j++ )
			{
				for(k=0;k<initials.size();k++ )
				{
					s=initials.get(k);
					state=new int[pea.length];
					System.arraycopy( s,0, state, 0, s.length );
					state[i]=pea[i].getInitial()[j];
					init.add(state);
				}
			}
			initials.clear();
			initials.addAll( init );
		}
		
		// verify existence
		
		i=0;
		while( i<initials.size() )
		{
			int s[]=initials.get(i);
			CDD inv=CDD.TRUE;
			for( j=0;j<s.length;j++ )
			{
				inv=inv.and( pea[j].getStateInvs()[s[j]] );
				if( inv==CDD.FALSE )
					break;
			}
			
			if( inv==CDD.FALSE )
			{
				initials.remove(i);
			}
			else
				i++;
		}
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
		for(int i=0;i<pea.length;i++)
		{
			alen+=pea[i].getActive(0).length;
		}
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
			
			if( doTest )
			{
				for( int ii=0;ii<pea[j].getActive(state[j]).length;ii++)
				{
					act[o]=pea[j].getActive(state[j])[ii];
					wait[o]=pea[j].getWaiting(state[j])[ii];
					exa[o++]=pea[j].getExact(state[j])[ii];
				}
			}
		}
		/*if( doTest )
		{
			test3.addDl( act, wait, exa );
			test1.addDl( s );
		}*/
		s+= " Clock Inv: "+ci;
		//if( doTest )
			//test2.addCInv( ci );
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
	
	
	
	
	/*public static void main(String[] args)
	{
		int i,n, num;
		int[] state=new int[20];
		int[] res;
		RTcheck8 ch=new RTcheck8( new Vector<PhaseEventAutomata>() );
		
		for(i=0;i<10000;i++ )
		{
			for(n=0;n<20;n++)
			{
				state[n]=(int)( Math.random()*30 );
			}
			
			num=ch.getBitNum( state );
			res=ch.getStateFromIdxMsk( num/32, 1<<(num%32) );
			
			for( n=0;n<state.length;n++ )
			{
				if( state[n]!=res[n] )
				{
					System.out.println( "Error!" );
				}
			}
		}
	}*/
}














