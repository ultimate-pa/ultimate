package RTconsistency;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.Vector;



public class z3Interface {
	
	final static String z3exe="C:\\Program Files\\Microsoft Research\\Z3-2.19\\bin\\z3.exe /smt2 /m /in";
	OutputStream stdin = null;
	Process p=null;
	BufferedReader input=null;
	Vector<String> allOutput;
	int lastreturned=-1;
	
	public int getLastreturned() {
		return lastreturned;
	}

	public z3Interface()
	{
		try {
		      String line;
		      allOutput=new Vector<String>();

		      p = Runtime.getRuntime().exec(z3exe);
		      input = new BufferedReader(new InputStreamReader(p.getInputStream()));
		      stdin = p.getOutputStream ();
		    }
		    catch (Exception err) {
		      err.printStackTrace();
		    }
	}
	
	private String lastline;
	
	public String write( String line )
	{
		try{
			System.out.println( line );
			stdin.write( line.getBytes() );
			stdin.flush();
			lastline=readLastLnFromInput();
			return lastline;
		}
	    catch (Exception err) {
	      err.printStackTrace();
	    }
	    return "";
	}
	
	public String readLastLn()
	{
		return lastline;
	}
	
	private String readLastLnFromInput()
	{
		String line=null;
		try{
			
			line = input.readLine();
			allOutput.add( line );
			lastreturned++;
		}
	    catch (Exception err) {
	      err.printStackTrace();
	    }
	    
	    return line;
	}
	
	public Vector<String> getAllOutputNoWait()
	{
		try{
			String line;
			while (input.ready() && (line = input.readLine()) != null) {
				allOutput.add(line);
			}
			
			//lastreturned=allOutput.size()-1;
		}
	    catch (Exception err) {
	      err.printStackTrace();
	    }
		return allOutput;
	}
	
	
	public boolean isSat()
	{
		try {
			Thread.sleep(20);
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		getAllOutputNoWait();
		
		String line=write("(check-sat)");
		if( line==null )
			return false;
		System.out.println( line );
		return line.compareTo("sat")==0;
		
	}
	
	private int countBraces( String line )
	{
		int res=0;
		for(int i=0;i<line.length();i++ )
		{
			if( line.charAt(i)=='(' )
				res++;
			else
				if( line.charAt(i)==')' )
					res--;
		}
		return res;
	}
	
	int modelPos=0;
	public String getModel()
	{
		try{
			modelPos=allOutput.size();
			String line=write("(model)");
			//allOutput.add( line );
			int cntb=countBraces( line );
			while ( cntb>0 ) {
				allOutput.add(line);
				cntb+=countBraces( line );
				if( !(input.ready() && (line = input.readLine()) != null ) )
				{
					break;
				}
			}
			
		}
	    catch (Exception err) {
	      err.printStackTrace();
	    }
	    return "";
	}
	
	public void close()
	{
		p.destroy();
	}
	
	
	public void printModel()
	{
		for( int i=modelPos;i<allOutput.size();i++ )
		{
			System.out.println( allOutput.get(i));
		}
	}
	
	public static void main(String[] args) {
		z3Interface z3=new z3Interface();
		z3.write("(set-logic QF_LRA)");
		//System.out.println( z3.readLastLn() );
		z3.write("(declare-fun x1_enter () Real)");
		z3.write("(declare-fun x2_enter () Real)");
		z3.write("(declare-fun time () Real)");

		z3.write("(declare-fun x1f () Real)");
		z3.write("(declare-fun x2f () Real)");
		z3.write("(assert (>= time 0.0))");
		z3.write("(assert (>= x1_enter 4.0))");
		z3.write("(assert (>= x2_enter 0.0))");
		z3.write("(assert (>= x1f 0.0))");
		z3.write("(assert (>= x2f 0.0))");
		z3.write("(assert (< x1_enter 10.0))");
		z3.write("(assert (= x2_enter 0.0))");
		z3.write("(assert (= (+ time x1_enter) x1f))");
		z3.write("(assert (= (+ time x2_enter) x2f))");
		z3.write("(assert (and (<= (+ x2_enter time) 6.0 ) (<= (+ x1_enter time) 10.0)))");
		z3.write("(assert (or (= (+ x2_enter time) 6.0 ) (= (+ x1_enter time) 10.0)))");
		z3.write("(assert (or (>= x2f 6.0) (and (>= x2f 6.0) (< x1f 10.0)) ))");
		z3.write("(assert (forall (y Real) (> y 0.0)):pat{(>= y 0.0)} )");
		//z3.write("(check-sat)");
		
		if( z3.isSat() )
		{
			z3.getModel();
			
			
			z3.write("(assert (not (or (>= x2f 6.0) (and (>= x2f 6.0) (< x1f 10.0)) )))");
			
			if( z3.isSat() )
			{
				System.out.println( z3.readLastLn() );
				
				z3.getModel();
			}
		}
		
		Vector<String> res=z3.getAllOutputNoWait();
		for( int i=0;i<res.size();i++ )
		{
			System.out.println( res.get(i) );
		}

	}

}
