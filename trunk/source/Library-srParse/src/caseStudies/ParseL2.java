package caseStudies;

import java.util.Vector;
import srParse.SRboolParser;
import srParse.SRboolLexer;
import java.io.*;
import pea.CDD;
import pea.BooleanDecision;
import org.antlr.runtime.*;

public class ParseL2 {
	
	private Vector<CDD> variables;
	
	private Vector<String> reqs;
	private int lstate;
	
	
	public ParseL2()
	{
		variables=new Vector<CDD>();
		reqs=new Vector<String>();
	}
	
	public Vector<String> getReqs()
	{
		return reqs;
	}
	
	public Vector<CDD> getVariables()
	{
		return variables;
	}
	
	
	 private void findVariables( String line)
	 {
		 SRboolLexer lex;
		 SRboolParser par;
		 lstate=0;
		 String[] buf;
		 buf=line.split( ", " );
		 int i;
		 buf[0]=buf[0].replaceFirst( "var ", "" );
		 buf[buf.length-1]=buf[buf.length-1].replace(";","");
		 for(i=0;i<buf.length;i++)
		 {
			 CDD cdd=null;
			 CharStream input = new ANTLRStringStream( buf[i] );
			 lex = new SRboolLexer( input );
			 
			 CommonTokenStream toks=new CommonTokenStream( lex );
			 par = new SRboolParser(toks);
			 
			 try
			 {
				// cdd=par.start();
			 }
			 catch( Exception e )
			 {
				 e.printStackTrace();
				 System.err.println( "Expression not recognized!" );
			 }
			 
			 //CDD cdd= BooleanDecision.create(buf[i]);
			 variables.add( cdd );
		 }
	 }
	
	public void parse( String file )
	{
		boolean in_comment=false;
		//URL url = new URL( "http://www.tutego.com/index.html" ); 
		try
		{
			FileInputStream strm=new FileInputStream(file);
			Reader reader = new InputStreamReader(strm);
			BufferedReader br= new BufferedReader(reader);
			
			String line,lbuf;
			lbuf=br.readLine();
			while( lbuf!=null )
			{
				//if( !in_comment )
				//{
					try{
						line=lbuf.split( "//")[0];
					}
					catch(Exception e)
					{
						line=lbuf;
					}
					//try{
					//	line=lbuf.split( "/*")[0];
					//}
					//catch(Exception e)
					//{
					//	line=lbuf;
					//}
				//}
				//else
				//{
				//	try{
				//		line=lbuf.split( "*/")[1];
				//		in_comment=false;
				//	}
				//	catch(Exception e)
				//	{
				//		continue;
				//	}
				//}
				
				if( line.length()>1 && !line.matches( "(\\s)*" ) )
				{
					int pos=line.indexOf( "var " );
					if( pos==0 )
					{
						findVariables( line );
					}
					else
					{
						reqs.add( line );
					}
				}
				
				lbuf=br.readLine();
			}
		}
		catch( Exception e)
		{
		}
	}
	

}
