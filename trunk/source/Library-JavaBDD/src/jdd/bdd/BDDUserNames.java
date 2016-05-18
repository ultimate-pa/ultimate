
package jdd.bdd;

/** BDD-style node naming: v1..vn  but also accepts names provided by the user */
public class BDDUserNames extends BDDNames {
	private String []names;
	public BDDUserNames() {
		names = new String[100];
		for(int i = 0; i < names.length; i++) names[i] = null;
	}

	public void setName(int index, String name) {
		if(index >= 0) {
			if(index >= names.length) grow(index+1);
			names[index] = name;
		}
	}

	public String variable(int n) {
		if(n < 0) return "(none)";
		if(n >= names.length) grow(n+1);
		if(names[n] != null) return names[n];
		return "v" + (n + 1);
	}

	private void grow(int size) {
		String []x = new String[size];
		for(int i = 0; i < x.length; i++) x[i] = null;
		for(int i = 0; i < names.length; i++) x[i] = names[i];
	}
}
