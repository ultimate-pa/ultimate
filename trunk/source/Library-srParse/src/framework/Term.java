package framework;

public class Term {

	//Attribute
	String Termvalue;
		
	public String getTermvalue() {
		return Termvalue;
	}

	//Constructors
	public Term(String Termvalue){
		this.Termvalue = Termvalue;
		//System.out.println("Term constructed with value " + Termvalue);
		}
	
	//Methods
	public boolean isElement(Term T){
		if (Termvalue.equals(T.Termvalue)){
			return true;
		}
		else return false;
	}
	
	
	//public static void main(String args []) {
		// TODO Auto-generated method stub
		//Term future = new Term ("future");
		//Term past = new Term ("past");
		//System.out.println(past.isElement(past));
		//System.out.println(past.isElement(future));
	//}
}


