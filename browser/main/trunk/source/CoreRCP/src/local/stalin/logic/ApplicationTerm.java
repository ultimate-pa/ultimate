package local.stalin.logic;


/**
 * Represents a function application term.  This consists of a function 
 * symbol and zero or more sub-terms (the parameters of the function).
 * A constant is represented as function application with zero parameters.
 * @author hoenicke
 *
 */
public class ApplicationTerm extends Term {
	private static final long serialVersionUID = 2097328726859042314L;
	FunctionSymbol function;
	Term[] parameters;

	ApplicationTerm(FunctionSymbol function, Term[] parameters) {
		this.function = function;
		this.parameters = parameters;
	}
	
	public FunctionSymbol getFunction() {
		return function;
	}

	public Term[] getParameters() {
		return parameters;
	}

	public boolean typeCheck() {
		if (function.getParameterCount() != parameters.length)
			return false;
		for(int i = 0; i < parameters.length; i++) {
			if (!parameters[i].typeCheck()
				|| parameters[i].getSort() != function.getParameterSort(i))
				return false;
		}
		return true;
	}

	public Sort getSort() {
		return function.getReturnSort();
	}

	public String toString() {
		String ann = getStringOfAnnotations();
		if (parameters.length == 0 && ann.equals(""))
			return function.getName();
		StringBuffer sb = new StringBuffer();
		sb.append("(");
		sb.append(function.getName());
		
		/* handle short-cut for repeated multiplication/addition*/
		if ((function.getName().equals("*")
			|| function.getName().equals("+"))
			&& parameters.length == 2) {
			ApplicationTerm app = this;
			while (app.parameters[1] instanceof ApplicationTerm
				   && ((ApplicationTerm) app.parameters[1]).function == function) {
				sb.append(" ").append(app.parameters[0]);
				app = (ApplicationTerm) app.parameters[1];
			}
			sb.append(" ").append(app.parameters[0]);
			sb.append(" ").append(app.parameters[1]);
		} else {
			for (Term t:parameters) {
				sb.append(" ").append(t);
			}
		}
		sb.append(ann);
		sb.append(")");
		return sb.toString();
	}

	@Override
	public boolean containsSubTerm(Term t) {
		if( t == this )
			return true;
		for( Term p : parameters )
			if( p == t )
				return true;
		return false;
	}
}
