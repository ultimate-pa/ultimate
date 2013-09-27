package RTconsistency;


import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Vector;

import pea.CDD;
import pea.*;
import AdvancedPea.AdvPea;
import RTconsistency.RTcheck4.GI;
import pea.*;
import java.util.*;

public class Reach1 {
	
	AdvPea[] pea;
	
	public Reach1( AdvPea[] peas )
	{
		pea=peas;
	}
	
	public boolean isReachable( int[] location )
	{
		int i,j;
		boolean res;
		CDD inv=CDD.TRUE;
		for(i=0;i<location.length;i++)
		{
			inv=CDD.TRUE;
			
			for(j=0;j<location.length;j++)
			{
				if( i!=j )
				{
					inv=inv.and( pea[j].getStateInvs()[location[j]] );
				}
			}
			
			Phase ph=new Phase( "Phase", inv );
			PhaseEventAutomata pea=new PhaseEventAutomata( "PEA", new Phase[]{ph}, new Phase[]{ph} );
			
			pea=pea.parallel( this.pea[i].getPea() );
			String lname= this.pea[i].getStateNames()[location[i]];
			res=false;
			for( int ii=0;ii<pea.getPhases().length;ii++)
			{
				if( pea.getPhases()[ii].getName().contains( lname ) )
				{
					res=true;
					break;
				}
			}
			if( !res )
				return false;
		}
		
		return true;
	}

}
