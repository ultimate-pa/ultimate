package local.stalin.automata.nfalibrary;

public class StateName extends StateContent {
	String name;
	
	StateName(String name){
		this.name=name;
		//TODO: Enforce that name !=null?
	}
	
	public String getName(){
		return this.name;
	}
	
	public String toString() {
		return this.name;
		//TODO: What happens, when name=null?
	}
}
