package pea;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;

/**
 * Pea Decision expressed by a BoogieAST Expression.
 * 
 * @author langenfeld
 * @see pea.Decision
 */
public class BoogieBooleanExpressionDecision extends Decision {
	
	private Expression expression;
	public Expression getExpression(){return this.expression;}
	
	/**
	 * 
	 * @param expression A Boogie expression which evaluates to boolean 
	 * but has no boolean expressions as children. 
	 */
	public BoogieBooleanExpressionDecision(Expression expression)
	{
		this.expression = expression;
		System.out.println(expression.toString());
	}
	
    /**
     * Create an boogie expression constraint and enclosing CDD
     * @param var the condition that must hold.
     */
    public static CDD create(Expression e) {
        return CDD.create(new BoogieBooleanExpressionDecision(e), 
        		CDD.trueChilds);
    }
	
	

	@Override
	public int compareTo(Object o) {
		if(!(o instanceof BoogieBooleanExpressionDecision)){
			return 1;
		}

		//TODO: is there somethin better than a string comparison for that
		return ((BoogieBooleanExpressionDecision)o).getExpression().toString()
						.compareTo(this.expression.toString());	

	}
	
    public boolean equals(Object o) {
        if (!(o instanceof BoogieBooleanExpressionDecision)) {
            return false;
        }
        if (!expression.equals(((BoogieBooleanExpressionDecision) o).getExpression())) {
            return false;
        }
        return true;
    }
    
    public int hashCode() {
        return expression.hashCode();
    }
	
	/**
	 * Transforms a BoggieExpressino to a BoogieExpression with primed Variable names 
	 *
	 */
	class BoogiePrimeIdentifierTransformer extends BoogieTransformer{
		private String ignore = new String();
		public void setIgnore(String ignore){
			if (ignore != null){
				this.ignore = ignore;
			}
		}
		
		@Override
		protected Expression processExpression(Expression expr){
			if(expr instanceof IdentifierExpression){
				if (this.ignore != null && ((IdentifierExpression)expr).getIdentifier().equals(this.ignore)){
					return super.processExpression(expr);
				}
				return new IdentifierExpression(expr.getLocation(),
						((IdentifierExpression) expr).getIdentifier()
						.replaceAll("([a-zA-Z_])(\\w*)","$1$2" + "'"));
			}
			return super.processExpression(expr);
		}
		
	}
	
	/**
	 * Transforms a BoggieExpressino to a BoogieExpression with unprimed Variable names 
	 *
	 */
	class BoogieRemovePrimeIdentifierTransformer extends BoogieTransformer{
		private String ignore = new String();
		public void setIgnore(String ignore){
			if (ignore != null){
				this.ignore = ignore;
			}
		}
		
		@Override
		protected Expression processExpression(Expression expr){
			if(expr instanceof IdentifierExpression){
				if (this.ignore != null && ((IdentifierExpression)expr).getIdentifier().equals(this.ignore)){
					return super.processExpression(expr);
				}
				return new IdentifierExpression(expr.getLocation(),
						((IdentifierExpression) expr).getIdentifier()
						.replaceAll("([a-zA-Z_])(\\w*)" + "'", "$1$2"));
			}
			return super.processExpression(expr);
		}
		
	} 

	@Override
	public Decision prime() {
		return this.prime(null);
	}

	@Override
	public Decision unprime() {
		return this.unprime(null);
	}
	
    @Override
    public Decision unprime(String ignore){
    	BoogieRemovePrimeIdentifierTransformer bpit = new BoogieRemovePrimeIdentifierTransformer();
    	bpit.setIgnore(ignore);
		Expression primed =  bpit.processExpression(this.expression);
		return new BoogieBooleanExpressionDecision(primed);
    }
    @Override
    public Decision prime(String ignore){
    	BoogiePrimeIdentifierTransformer bpit = new BoogiePrimeIdentifierTransformer();
    	bpit.setIgnore(ignore);
		Expression primed =  bpit.processExpression(this.expression);
		return new BoogieBooleanExpressionDecision(primed);
    }

	@Override
	public String toString(int child) {
		if(child != 0){
			BoogieLocation loc = new BoogieLocation("",0,0,0,0,false);
			return BoogiePrettyPrinter.print(new UnaryExpression(
					loc,
				    UnaryExpression.Operator.LOGICNEG,
				    this.expression));
		}
		return BoogiePrettyPrinter.print(this.expression);
	}

	@Override
	public String toSmtString(int child) {
		return null;
	}

	@Override
	public String toTexString(int child) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String toUppaalString(int child) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String toUppaalStringDOM(int child) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getVar(){
		throw new RuntimeException("getVar not supported by BoogieBooleanExpressionDecision (use getVars)!");
	}
	
	/**
	 * Collects all identifier statements from a boogie expression
	 */
	class BoogieIdentifierCollector extends BoogieVisitor{
		
		private ArrayList<IdentifierExpression> identifiers = new ArrayList<IdentifierExpression>();
		private BoogieType aproxType = BoogieType.TYPE_BOOL;
		
		@Override
		protected void visit(IdentifierExpression expr) {
			this.identifiers.add(expr);
		}
		@Override
		protected void visit(RealLiteral expr) {
			this.aproxType = BoogieType.TYPE_REAL;
		}
		@Override
		protected void visit(BooleanLiteral expr) {
			this.aproxType = BoogieType.TYPE_BOOL;
		}
		@Override
		protected void visit(IntegerLiteral expr) {
			this.aproxType = BoogieType.TYPE_INT;
		}
		
		public ArrayList<IdentifierExpression> getIdentifiers(Expression expr){
			this.processExpression(expr);
			
			//try to find a solution to what type the variables of the expression are, by giving them
			//simply the type of type the literals in the expression had.
			//TODO: get a better solution for this!
			for(IdentifierExpression ident: this.identifiers){
				if(ident.getType() == null){
					ident.setType(this.aproxType);
				}
			}
			return identifiers;
		}
		
	}
	
	/**
	 * Collects variable names and types from the expression.
	 * @return Map: ident -> type
	 */
	public Map<String,String> getVars(){
		Map<String,String> vars = new HashMap<String,String>();
		
		BoogieIdentifierCollector collector = new BoogieIdentifierCollector();
		ArrayList<IdentifierExpression> idents = collector.getIdentifiers(this.expression);
		
		for(IdentifierExpression ident: idents){
			vars.put(ident.getIdentifier().toString(), ident.getType().toString());
		}
		
		return vars;
	}

}
