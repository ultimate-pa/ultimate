package caseStudies;

import java.util.Vector;

import MayBeDeleted.PL_PatternToLogic;

public class InconsistentExample {
	
	static PL_PatternToLogic checker = new PL_PatternToLogic();
	
	
	public static Vector<String> inconsistentExample1(){
		Vector<String> inconsistentReqSet = new Vector<String>();
		
		//beteiligte Variablen im ReqSet
		String voltage5 = "voltage >= 5";
		String voltage6 = "voltage = 6";
		String voltage7 = "((voltage >= 7) | (voltage < 5))";
		String setErrorAllowed = "SetErrorAllowed = 1";
		String setVoltageError = "SetVoltageError = 1";
		String VoltageError = "VoltageError = 1";
		
		//inkonsistentes ReqSet
		String req1 = "After \""+voltage5+"\" until \""+voltage7+"\", it is never the case that \""+setErrorAllowed+"\" holds";
		String req2 = "Globally, it is always the case that if \"!"+setErrorAllowed+"\" holds, then \"!"+setVoltageError+"\" holds as well";
		String req3 = "Globally, it is always the case that if \""+setVoltageError+"\" holds, then \""+VoltageError+"\" eventually holds";
		String req4 = "Globally, it is always the case that if \""+voltage6+"\" holds, then \""+setVoltageError+"\" holds as well";
		
		inconsistentReqSet.addElement(req1);
		inconsistentReqSet.addElement(req2);
		inconsistentReqSet.addElement(req3);
		inconsistentReqSet.addElement(req4);
		
		return inconsistentReqSet;
	}
	
	public static Vector<String> inconsistentExample2(){
		Vector<String> inconsistentReqSet = new Vector<String>();
		
		//beteiligte Variablen im ReqSet
		String setErrorAllowed = "SetErrorAllowed = 1";
		String setVoltageError = "SetVoltageError = 1";
		String VoltageError = "VoltageError = 1";
		
		//inkonsistentes ReqSet
		String req2 = "Globally, it is always the case that if \"!"+setErrorAllowed+"\" holds, then \"!"+setVoltageError+"\" holds as well";
		String req3 = "Globally, it is always the case that if \""+setVoltageError+"\" holds, then \""+VoltageError+"\" eventually holds";
		String req4 = "Globally, it is always the case that if \""+VoltageError+"\" holds, then \""+setVoltageError+"\" holds as well";
		
		inconsistentReqSet.addElement(req2);
		inconsistentReqSet.addElement(req3);
		inconsistentReqSet.addElement(req4);
		
		return inconsistentReqSet;
	}
	
	public static Vector<String> inconsistentExample3(){
		Vector<String> inconsistentReqSet = new Vector<String>();
		
		//beteiligte Variablen im ReqSet
		String setErrorAllowed = "SetErrorAllowed = 1";
		
		//inkonsistentes ReqSet
		String req1 = "Globally, it is always the case that \""+setErrorAllowed+"\" holds";
		String req2 = "Globally, it is never the case that \""+setErrorAllowed+"\" holds";
		
		inconsistentReqSet.addElement(req2);
		inconsistentReqSet.addElement(req1);
		
		return inconsistentReqSet;
	}
	
	public static void forAll(Vector<String> requirementsSet){
		String s1 = "";
		String s2 = "";
		String s3 = "";
		String s = "";
		String t = checker.getSpecInLTL(requirementsSet);
		//String t = "test";
		Vector<String> all = new Vector<String>();
		for (int i =0; i<2; i++){
			s1 = "(SetErrorAllowed ="+i+")";
			for (int j =0; j <2; j++){
				s2 = "(SetVoltageError ="+j+")";
				for (int k=0; k<2; k++){
					s3 = "(VoltageError ="+k+")";
					s = "("+s1+" & "+s2+" & "+s3+" & "+t+")";
					all.addElement(s);
				}
			}
		}
		String result = "";
		if (all.size()>0){
			result = all.get(0);
			for (int i=1; i<all.size(); i++){
				result = result +" & "+ all.get(i);
			}
		}		
		System.out.println(result);
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		Vector<String> inc = inconsistentExample2();
		checker.getSpecInLTL(inc);
		forAll(inc);
		
		Vector<String> inc2 = inconsistentExample3();
		checker.getSpecInLTL(inc2);
	}

}
