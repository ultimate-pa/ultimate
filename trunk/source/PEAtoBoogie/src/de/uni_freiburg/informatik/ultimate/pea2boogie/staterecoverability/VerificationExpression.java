package de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability;

import javax.management.RuntimeErrorException;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;

public class VerificationExpression {
	private final String[] expr;
	private final String dataType;
	private final int iVariable = 0;
	private final int iOperator = 1;
	private final int iValue = 2;

    public VerificationExpression(String[] expr, String dataType) {
        this.expr = expr;
        this.dataType = dataType;
    }
    public String[] getExpr() {
        return expr;
    }
    
    public String getVariable() {
    	return expr[iVariable];
    }
    
    public String getOperator() {
    	return expr[iOperator];
    }
    
    public String getValue() {
    	return expr[iValue];
    }
    
    public String getDataType( ) {
    	return dataType;
    }

    public boolean getBoolValue() {
    	if(expr[iValue].equals(VerificationExpressionContainer.BOOL)) {
    		return Boolean.getBoolean(expr[iValue]);
    	}

    	throw new RuntimeErrorException(null, getClass().getName() + " data type " + dataType + " is not correct for " + expr);
    }
    
    public int getIntegerValue() {
    	if(expr[iValue].equals(VerificationExpressionContainer.INT)) {
    		return Integer.getInteger(expr[iValue]);
    	}

    	throw new RuntimeErrorException(null, getClass().getName() + " data type " + dataType + " is not correct for " + expr);
    }
    
    public double getDoubleValue() {
    	if(expr[iValue].equals(VerificationExpressionContainer.REAL)) {
    		return Double.parseDouble(expr[iValue]);
    	}

    	throw new RuntimeErrorException(null, getClass().getName() + " data type " + dataType + " is not correct for " + expr);
    }
    
    public BoogiePrimitiveType getBoogiePrimitiveType() {
    	switch (dataType) {
		case "bool":
			return BoogiePrimitiveType.TYPE_BOOL;
		case "int":
			return BoogiePrimitiveType.TYPE_INT;
		case "real":
			return BoogiePrimitiveType.TYPE_REAL;
		default:
			return BoogiePrimitiveType.TYPE_ERROR;
		}
    }
}
