package local.stalin.logic;

import java.io.ObjectStreamException;

/**
 * This class is the super class of all Atoms.  There are only two instances
 * of atom, namely Atom.TRUE and Atom.FALSE.  All other atoms are instances
 * of sub classes of atoms.
 * 
 * @author hoenicke
 */
public class Atom extends Formula {
	private static final long serialVersionUID = 3296538093042200037L;
	public static final Atom TRUE = new Atom() {
		private static final long serialVersionUID = -2067625621090390323L;

		private Object readResolve() throws ObjectStreamException {
			return Atom.TRUE;
		}
	};
	public static final Atom FALSE = new Atom() {
		private static final long serialVersionUID = -2739676132535780263L;

		private Object readResolve() throws ObjectStreamException {
			return Atom.FALSE;
		}
	};
	
	protected Atom() {
	}

	public boolean typeCheck() {
		return true;
	}

	public String toString() {
		String rep;
		String ann = getStringOfAnnotations();
		if (this == TRUE)
			rep = "true";
		else if (this == FALSE)
			rep = "false";
		else
			rep = super.toString();
		if (ann != "")
			return "("+rep+ann+")";
		else
			return rep;
	}
}
