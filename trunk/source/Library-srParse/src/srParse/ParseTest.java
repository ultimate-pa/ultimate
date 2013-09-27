package srParse;

import pea.*;
import java.lang.management.*;
import PatternLanguage.PL_Pattern2Logic;
import PatternLanguage.PL_initiatedPattern;
import caseStudies.DependencyAnalyse;
import caseStudies.J2UPPAALConverterSR;
import caseStudies.SimpleDlFind;
import pea.reqCheck.PatternToPEA;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Reader;
import org.antlr.runtime.*;
import RTconsistency.*;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import pea.modelchecking.DOTWriter;
import pea.modelchecking.J2UPPAALConverter;

import java.util.Vector;

import pea.*;

public class ParseTest {

	private static int renamePhases( PhaseEventAutomata pea, int firstIdx)
	{
		int i;
		for( i=0;i<pea.getPhases().length;i++ )
		{
			Phase p=pea.getPhases()[i];
			p.setName( "st"+firstIdx );
			firstIdx++;
		}
		return firstIdx;
	}
	
	
	public static long getCpuTime( ) {		
	    ThreadMXBean bean = ManagementFactory.getThreadMXBean( );
	    return bean.isCurrentThreadCpuTimeSupported( ) ?
	        bean.getCurrentThreadCpuTime( ) : 0L;
	}

	
	
	public static void main(String[] args) {
		int globalStId=0;
		
		
		Vector<Integer> patternStateIds=new Vector<Integer>();
		
		try{
		//CharStream cs = new ANTLRFileStream("C:\\daten\\test1\\reqs4.txt");
		//CharStream cs = new ANTLRFileStream("C:\\daten\\test1\\accreqs2.req");
		//CharStream cs = new ANTLRFileStream("C:\\daten\\test1\\ind_set_0___.req");
		//CharStream cs = new ANTLRFileStream("C:\\daten\\test1\\counterex1.req");
		//CharStream cs = new ANTLRFileStream("C:\\daten\\test3\\accreqs2.req");
	
		//	run("C:\\daten\\test1\\reqs4.txt");
		//	run("C:\\daten\\test1\\Lambda.reqind_set_2.req");
		//	run("C:\\daten\\test1\\accreqs2.req");
			//run("C:\\daten\\test3\\accreqs3.req");
			//run("C:\\daten\\test3\\accreqs4.req");
			run("C:\\daten\\test1\\hybrid2_extended.req");
			//run("C:\\daten\\test3\\hybrid2.req");
		//	run("C:\\daten\\test1\\accreqs2.req");
			//run("C:\\daten\\test1\\counterex1.req");
		//	run("C:\\daten\\test1\\reqs4.txt");
	//		run("C:\\daten\\test1\\ind_set_0_____.req");
	//		run("C:\\daten\\test2\\hybrid_ALL.req");
		
			//run( "C:\\daten\\test1\\New Folder (3)\\accreqs2.reqind_set_0.req" );
		//	run( "C:\\daten\\test1\\New Folder (2)\\hybrid1.req" );
			
			
			//run( "C:\\daten\\CaseStudy1\\deploy1.req" );
			//run( "C:\\daten\\CaseStudy1\\deploy1.reqind_set_2.req" );
			
			
			//run("C:\\daten\\test4\\sample1.req");
		}
		catch(Exception e)
		{}
	}
	
	
	public static void run( String filename )
	{
		int globalStId=0;
		
		
		Vector<Integer> patternStateIds=new Vector<Integer>();
		
		try{
		CharStream cs = new ANTLRFileStream( filename );
		SRboolLexer l=new SRboolLexer(cs);
		
		TokenStream tokens = new CommonTokenStream(l);
		//tokens.setTokenSource(l);
		
		SRboolParser p=new SRboolParser(tokens);
		
		try{
			try {
				p.file();
			} catch (ENotDeclaredIdentifier e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				
				throw new Exception();
			}
			
			long startGlob=getCpuTime();
			
			srParseController contr=srParseController.getInstance();
			Vector<srParsePattern> patterns=contr.getPatterns();
			int i;
			PhaseEventAutomata pea=null;
			//PL_initiatedPattern initPat;
			//PL_Pattern2Logic toLogic = new PL_Pattern2Logic();
			
			DependencyAnalyse depana=new DependencyAnalyse();
			
			Vector<srParsePattern> pat=(Vector<srParsePattern>)patterns.clone();
			Vector<Vector<srParsePattern>> indsets=depana.patternAnalysis( pat );
			
			Vector<PhaseEventAutomata> peas=new Vector<PhaseEventAutomata>();
			
			long startPar=getCpuTime();
			System.out.println( "Number of independend sets: " +indsets.size()  );
			int cnt=0;
			for( i=0;i<indsets.size();i++)
			{
				Set<srParsePattern> s=new HashSet<srParsePattern>( );
				s.addAll(indsets.get(i));
				BufferedWriter f = new BufferedWriter(new OutputStreamWriter( new FileOutputStream(filename+"ind_set_"+i+".req"), "UTF8"));
				
				Iterator<srParsePattern> it=s.iterator();
				while(it.hasNext())
				{
					srParsePattern pattern = it.next();
					f.write( pattern.toString()+"\r\n" );
					cnt++;
				}
				f.flush();
				f.close();
			}
			
			
			if( cnt!=patterns.size() )
			{
				System.err.println( "##############" );
				System.err.println( "" );
				System.err.println( "" );
				System.err.println( " cnt!=patterns.size" );
				System.err.println( "cnt: "+cnt );
				System.err.println( "patterns.size(): "+ patterns.size() );
				System.err.println( "" );
				System.err.println( "" );
				System.err.println( "###############" );
			}
			
			PatternToPEA peaTrans=new PatternToPEA();
			//Set<PhaseEventAutomata> peas=new HashSet<PhaseEventAutomata>();
			
			for(i=0;i<patterns.size();i++ )
			{
				patterns.get(i).setPeaTransformator( peaTrans );
				if( pea==null )
				{
					pea=patterns.get(i).transformToPea();
				
					
					//globalStId=renamePhases(pea, globalStId );
					//renamePhases(pea, 0 );
					patternStateIds.add(globalStId);
					
					peas.add( pea );
					
			//		DOTWriter dotwriter2 = new DOTWriter(filename+"_0.dot", pea);
			//		dotwriter2.write();
					
					System.out.println( "Parallel: 0" );
					
					//J2UPPAALConverter j2uppaalWriterx = new J2UPPAALConverter();
				    //j2uppaalWriterx.writePEA2UppaalFile("c:/daten/test1/ParseTest_0.xml", pea);
					
				}
				else
				{	
					PhaseEventAutomata pea2=patterns.get(i).transformToPea();
					
					
					if( pea2==null )
						continue;
					
					//globalStId=renamePhases(pea2, globalStId );
					
					//renamePhases(pea2, 0 );
					patternStateIds.add(globalStId);
					
			//		DOTWriter dotwriter2 = new DOTWriter(filename+"_"+i+".dot", pea2);
			//		dotwriter2.write();
					System.out.println( "Parallel: "+i );
					
					peas.add( pea2 );
					
					//J2UPPAALConverter j2uppaalWriterx = new J2UPPAALConverter();
				    //j2uppaalWriterx.writePEA2UppaalFile("c:/daten/test1/ParseTest_"+i+".xml", pea2);
					 
			//		pea=pea.parallel( pea2 );
				}
				
				//initPat=patterns.get(i).getInitiatedPattern();
				//toLogic.transformPatternToLogic( initPat, "DC" );
				
			}
			
			/*CDD nvos=BooleanDecision.create("Video_Operating_State");
			CDD declreq=BooleanDecision.create("deceleration_request");
			CDD cond=nvos.and(declreq);
			cond=cond.negate();
			for( i=0;i<pea.getPhases().length;i++ )
			{
				if( !pea.getPhases()[i].getStateInvariant().implies(cond) )
				{
					String init="";
					if( pea.getPhases()[i].isInit() )
					{
						init="Initial ";
					}
					System.out.println( init+"cond holds in Location " + pea.getPhases()[i] + "( "+pea.getPhases()[i].getStateInvariant()+" ) "+i );
				}
			}*/
			
			long durPar=getCpuTime()-startPar;
			
			
			
			/*i=0;
			while( peas.size()>1 )
			{
				Set<PhaseEventAutomata> peas_old=peas;
				Iterator<PhaseEventAutomata> it=peas_old.iterator();
				peas=new HashSet<PhaseEventAutomata>();
				PhaseEventAutomata pe=null;
				while(it.hasNext())
				{
					pe=it.next();
					if( it.hasNext() )
					{
						pe=pe.parallel( it.next() );
						System.out.println( "Parallel: "+i++ );
						
					}
					
					peas.add(pe);					
				}
			}
			
			pea=peas.iterator().next();*/
			
			
			System.err.println("RTcheck1");
			long start1=getCpuTime();
			RTcheck1 ch=new RTcheck1( );
			//ch.setMessageFile( "c:\\daten\\test1\\RTcheck4_out.txt" );
			
			//for(int k=0;k<peas.size();k++)
			{
			//	ch.checkPea( pea );
			}
			
			long dur1=getCpuTime()-start1;
			
			
			
			
			
		//	DOTWriter dotwriter2 = new DOTWriter(filename+".dot", pea);
		//	dotwriter2.write();
			
			
			
			RTcheck8 ch8=new RTcheck8( peas );
		
			
			
			
			System.err.println("RTcheck6 - implicit search");
			long start6=getCpuTime();
			RTcheck6 ch6=new RTcheck6( peas );
			Set<int[]> minDeadlocks=new HashSet<int[]>();
			ch6.setMinDeadlocks( minDeadlocks );
//		//	ch6.setMinDeadlocks( ch9.minDeadlocks );
			
			ch6.setMessageFile( filename+"out6.txt" );
			ch6.check();
			
			long dur6=getCpuTime()-start6;
			
			
			
			
			
			
			System.err.println("RTcheck8 - symbolic BF-search");
			long start8=getCpuTime();
			
			
			ch8.setMessageFile( filename+"out8.txt" );
			ch8.check();
			
			long dur8=getCpuTime()-start8;
			
			
			System.err.println("RTcheck9 - symbolic BF-search");
			long start9=getCpuTime();
			
		/*	
			//ch9.setMessageFile( filename+"out9.txt" );
			ch9.exportMinDlAutomata( "c:\\daten\\test1\\minDlAutomata" );
			ch9.exportMinDlAutomataMinPath( "c:\\daten\\test1\\minDlAutomataPath" );
			
			//for( int k=0;k<ch9.minDeadlocks.size();k++ )
			{
				Vector<int[]> tr=new Vector<int[]>();
				int[] v1={-1,-1,-1,0,-1,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,2};
				int[] v2={-1,-1,-1,0,-1,1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,1};
				tr.add(v1);
				tr.add(v2);
				ch9.findSuperTraceWithoutClock( tr );
			}
			
			
			long dur9=getCpuTime()-start9;*/
			
			
			System.err.println("RTcheck10 - BMC on explicit PEA");
			long start10=getCpuTime();
			
			RTcheck10 ch10=new RTcheck10(2);
			//ch10.check( pea, filename+"out10.smt" );
			
			long dur10=getCpuTime()-start10;
			
			
			
			System.err.println("RTcheck12 - DBMC on explicit PEA");
			long start12=getCpuTime();
			
			final int num=0;
			
		/*	int j=0;
			for( j=0;j<num;j++)
			{
				RTcheck12 ch12=new RTcheck12();
				ch12.setSmtFile( filename+"out12_"+j+"_.smt" );
				ch12.check( pea );
			}
			
			BufferedWriter smtFile=null;
			try {
				//messageFile=new BufferedWriter(new FileWriter(filename,"UTF8"));
	    		smtFile = new BufferedWriter(new OutputStreamWriter( new FileOutputStream(filename+"_check.bat"), "UTF8"));
	    		for( j=0;j<num;j++ )
	    		{
	    			smtFile.write( "\"C:\\Program Files\\Microsoft Research\\Z3-2.9\\bin\\z3.exe\" /smt2 /m \""+filename+"out12_"+j+"_.smt\" > out_"+j+"_.txt \r\n" );
	    		}
	    		smtFile.flush();
	    		smtFile.close();
	    		Runtime.getRuntime().exec(filename+"_check.bat");
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			*/
			long dur12=getCpuTime()-start12;
			
			
			System.err.println("RTcheck13 - BMC");
			long start13=getCpuTime();
			
			//final int num=5;
			
			//int j=0;
			
	//		RTcheck13 ch13=new RTcheck13(1);
	//		ch13.setMindeadlocks( minDeadlocks );
	//		ch13.check( peas.toArray(new PhaseEventAutomata[0]), filename+"out13.smt", contr.getVariables() );
			
			long dur13=getCpuTime()-start13;
			
			
			/*
			System.err.println("RTcheck14 - fully symbolic DBMC");
			long start14=getCpuTime();
			
			final int num=5;
			
			int j=0;
			for( j=0;j<num;j++)
			{
				RTcheck14 ch14=new RTcheck14();
				if( ch14.check( pea ) )
					break;
			}
			
			
			long dur14=getCpuTime()-start14;
			*/
			
			
			
			
			
			/*System.err.println("RTcheck12 - DBMC on explicit PEA");
			long start13=getCpuTime();
			
			RTcheck13 ch13=new RTcheck13(5);
			ch13.check( peas.toArray(new PhaseEventAutomata[0]), filename+"out13.smt" );
			
			long dur13=getCpuTime()-start13;*/
			
			
			
			
			
			
		//	J2UPPAALConverter j2uppaalWriter = new J2UPPAALConverter();
    	//	j2uppaalWriter.writePEA2UppaalFile(filename+".xml", pea);
		    
			
			 
			
			/*long start;
			RTcheck3 check=new RTcheck3();
			check.setMessageFile("c:\\daten\\test1\\RTcheck.txt");
			
			System.err.println("RTconsistency check");
			start=System.nanoTime();
			check.checkPea( pea );
			long dur1=System.nanoTime()-start;
			System.err.print( ((double)dur1/1000/1000) );
			System.err.println( " m seconds" );*/
			
			/*RTcheck5 check=new RTcheck5();
			check.setMessageFile("c:\\daten\\test1\\RTcheck.txt");
			
			System.err.println("RTconsistency check");
			start=System.nanoTime();
			check.checkPea( pea );
			long dur1=System.nanoTime()-start;
			System.err.print( ((double)dur1/1000/1000) );
			System.err.println( " m seconds" );*/
			
			
			/*RTcheck1 ch1=new RTcheck1();
			ch1.checkPea( pea );
			
			start=System.nanoTime();
		     SimpleDlFind dlf=new SimpleDlFind();
		     Vector<SimpleDlFind.FoundEntry> st=dlf.doDlFind( pea );
		     long dur2=System.nanoTime()-start;
		     
			System.err.print("Simple DlFind detected ");
		     System.err.print( st.size() );
		     System.err.print(" deadlocks in ");
		     System.err.print( ((double)dur2/1000/1000) );
		     System.err.println( " m seconds" );
		     for( i=0;i<st.size();i++ )
		     {
		    	 System.err.print( "Simple DlFind detected " );
		    	// System.err.print( st.elementAt(i) );
		    	 System.err.println( st.elementAt(i).toString() );
		     }
			
			//System.out.println( patterns.size() );*/
			
		    
		    long endGlob= getCpuTime();
		    System.out.println( "Programm time: " + ( endGlob-startGlob )/1000000 + "ms for file: "+filename );
		    
		    
		    System.out.print( "RTcheck8 duration: "+((double)dur8/1000/1000) );
			System.out.println( " m seconds" );
			
			System.out.print( "RTcheck6 duration: "+((double)dur6/1000000) );
			System.out.println( " m seconds" );
			
			System.out.print( "RTcheck1 duration:" + ((double)dur1/1000000) );
			System.out.println( " m seconds" );
			
			System.out.print( "Parallel duration:" + ((double)durPar/1000000) );
			System.out.println( " m seconds" );
			
			
		}
		catch(Exception e)
		{
			e.printStackTrace();
		}
		}
		catch(Exception e)
		{
			e.printStackTrace();
		}
		
		
	}
	
	

}
