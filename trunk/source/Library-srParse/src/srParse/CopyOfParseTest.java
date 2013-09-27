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

public class CopyOfParseTest {

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
		//	run("C:\\daten\\test1\\accreqs1_extended.req");
		//	run("C:\\daten\\test1\\accreqs2.req");
			run("C:\\daten\\test1\\accreqs3.req");
			//run("C:\\daten\\test1\\accreqs4.req");
			//run("C:\\daten\\test1\\hybrid1.req");
			//run("C:\\daten\\test1\\hybrid2.req");
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
			
			
			for(i=0;i<patterns.size();i++ )
			{
				
			}
			
			PhaseEventAutomata pea=null;
			
			DependencyAnalyse depana=new DependencyAnalyse();
			
			Vector<srParsePattern> pat=(Vector<srParsePattern>)patterns.clone();
			Vector<Vector<srParsePattern>> indsets=depana.patternAnalysis( pat );
			
			Vector<PhaseEventAutomata> peas=new Vector<PhaseEventAutomata>();
			
			long startPar=getCpuTime();
			System.out.println( "Number of independend sets: " +indsets.size()  );
			int cnt=0;
			if( indsets.size()>1 )
			{
				for( i=0;i<indsets.size();i++)
				{
					Set<srParsePattern> s=new HashSet<srParsePattern>( );
					s.addAll(indsets.get(i));
					BufferedWriter f = new BufferedWriter(new OutputStreamWriter( new FileOutputStream(filename+"ind_set_"+i+".req"), "UTF8"));
					
					Iterator<srParsePattern> it=s.iterator();
					f.write( "nodeclare;\r\n" );
					while(it.hasNext())
					{
						srParsePattern pattern = it.next();
						f.write( pattern.toString()+"\r\n" );
						cnt++;
					}
					f.flush();
					f.close();
					//
				}
				
				return;
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
			
			for(i=0;i<patterns.size();i++ )
			{
				patterns.get(i).setPeaTransformator( peaTrans );
				if( pea==null )
				{
					pea=patterns.get(i).transformToPea();
					peas.add( pea );					
					System.out.println( "Parallel: 0" );
				}
				else
				{	
					PhaseEventAutomata pea2=patterns.get(i).transformToPea();
					
					if( pea2==null )
						continue;
					
					System.out.println( "Parallel: "+i );
					
					peas.add( pea2 );
					
					// Parallelautomat explizit aufbauen 
			//		pea=pea.parallel( pea2 );
				}
			}
			
			
			long durPar=getCpuTime()-startPar;
			
			
			System.err.println("RTcheck1");
			long start1=getCpuTime();
			RTcheck1 ch=new RTcheck1( );
			
			// D_1 SUche auf explizitem Parallelautomat
			//	ch.checkPea( pea );
			
			
			long dur1=getCpuTime()-start1;
			
			
			
			
			RTcheck8 ch8=new RTcheck8( peas );
			
			// implizite D_0 Suche
			System.err.println("RTcheck6 - implicit search");
			long start6=getCpuTime();
			RTcheck6 ch6=new RTcheck6( peas );
			Set<int[]> minDeadlocks=new HashSet<int[]>();
			ch6.setMinDeadlocks( minDeadlocks );
			
			ch6.setMessageFile( filename+"out6.txt" ); // ausgabedatei
			ch6.check(); // D_0 Suche durchführen
			
			long dur6=getCpuTime()-start6;
			
			
			
			
			
			
			System.err.println("RTcheck8 - symbolic BF-search");
			long start8=getCpuTime();
			
			ch8.minDeadlocks=minDeadlocks; // menge der D_0 Deadlocks übergeben
			ch8.setMessageFile( filename+"out8.txt" ); // ausgabedatei
			ch8.check(); // Breitensuche auf implizitem PEA nach den bekannte D_0 Deadlocks durchführen
			
			long dur8=getCpuTime()-start8;
			
			
			System.err.println("RTcheck10 - BMC on explicit PEA");
			long start10=getCpuTime();
			
			RTcheck10 ch10=new RTcheck10(5); // parameter ist k - Anzahl der Schritte
			
			long dur10=getCpuTime()-start10;
			
			
			
			System.err.println("RTcheck12 - DBMC on explicit PEA");
			long start12=getCpuTime();
			
			final int num=5000; // anzahl der zu prüfenden pfade
			
			// einkommentieren falls dbmc auf explizitem PEA verwendet werden soll
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
			
			
			
			
			
			
			
			// expliziten Parallelautomat als Uppaal TA ausgeben
		//	J2UPPAALConverter j2uppaalWriter = new J2UPPAALConverter();
    	//	j2uppaalWriter.writePEA2UppaalFile(filename+".xml", pea);
		    
			
		    
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
