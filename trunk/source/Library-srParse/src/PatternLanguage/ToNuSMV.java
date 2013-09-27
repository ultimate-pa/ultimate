package PatternLanguage;

import java.util.regex.Pattern;

public class ToNuSMV {
	
	//Constructor ist leer
	public ToNuSMV(){		
	}

	//Diese Klasse sollte automatisch getexte Formeln durchgehen, und in NuSMV-Syntax übersetzen.
	
	String test1 = "AG(P ! EF S )";
	// A(((P ! E[(¬R ) U (S ^¬R )]) _
	
	//Der String A(x W y) = !E(!y U (!x & !y))
	public String replace_AW_inCTL(String x, String y){
		String result = ("!E[!("+y+") U (!("+x+") & !("+y+"))]");
		//System.out.println("For String "+x+" and String "+y+ " the formula A("+x+" W "+y+") is equivalent to " + result);
		return result;
	}
	
	// Splitted einen String sentence auf, so dass alle Teile, die durch "W" abgetrennt sind, 
	// in einen neuen ArrayString gepackt werden, und liefert den zurück		
	public String[] getSplittedSentence(String sentence){
		// Create a pattern to match breaks
        Pattern p = Pattern.compile("(\\s*\"|\"\\s*)+");
        // Split input with the pattern
        String[] result = 
                 p.split(sentence);
        return result;
    }
	
	// & Globally & n.a. & \red$\texttt{AG(\textit{P}} \rightarrow \texttt{EF \textit{S})}$ & \red$\texttt{AG(\textit{P}} \rightarrow \texttt{EF \textit{S})}$\\
	//\cline{2-5}
	//Replace "!" with "->"
	public String transformFromTexToSMVSyntax(String s){
		s = s.replace("\red", "");
		s = s.replace("\texttt{", "");
		s = s.replace("\textit{", "");
		s = s.replace("}", "");
		s = s.replace("$", "");
		s = s.replace("&", ";");
		s = s.replace("\rightarrow", " -> ");
		s = s.replace("\\wedge", " & ");
		s = s.replace("\neg", "!");
		s = s.replace("P", "(\"+p+\")");
		s = s.replace("Q", "(\"+q+\")");
		s = s.replace("R", "(\"+r+\")");
		s = s.replace("S", "(\"+s+\")");
		s = s.replace("T", "(\"+t+\")");
		s = s.replace("Z", "(\"+z+\")");
		s = s.replace("[", "(");
		s = s.replace("]", ")");

		System.out.println(s);
		return s;
	}
	public void replaceXwithY(String regex, String replacement){
		
	}
	
	//AG(P! EFc S )
	//Diese Funktion transformiert LaTex-Formeln, die aus dem AcrobatReader kopiert wurden, in die NuSMV Syntax
	public String transformToSMVSyntax(String s){
		
		//wenn es ein W enthält, dann muß der String noch weiter verändert werden, da NuSMV kein W unterstützt
		if (s.contains("W")){
			s = s.replace("!", "->");
			//s = s.replace("[", "(");
			//s = s.replace("]", ")");
			s = s.replace("^", "&");
			s = s.replace("¬", "!");
			s = s.replace("_", "|");
			s = s.replace("EF", "EBF 0..");
			s = s.replace("EG", "EBG 0..");
			s = s.replace("AF", "ABF 0..");
			s = s.replace("AG", "ABG 0..");
			s = s.replace("U", "BU 0..");
			//s = s.replace("c", "\"+c+\"");
		}
		else
		{
			s = s.replace("!", "->");
			s = s.replace("P", "(\"+p+\")");
			s = s.replace("Q", "(\"+q+\")");
			s = s.replace("R", "(\"+r+\")");
			s = s.replace("S", "(\"+s+\")");
			s = s.replace("T", "(\"+t+\")");
			s = s.replace("Z", "(\"+z+\")");
			//s = s.replace("[", "(");
			//s = s.replace("]", ")");
			s = s.replace("^", "&");
			s = s.replace("¬", "!");
			s = s.replace("_", "|");
			s = s.replace("EF", "EBF 0..");
			s = s.replace("EG", "EBG 0..");
			s = s.replace("AF", "ABF 0..");
			s = s.replace("AG", "ABG 0..");
			s = s.replace("U", "BU 0..");
			//s = s.replace("c", "\"+c+\"");
			s.replace("W", "V");
		}
		System.out.println(s);
		return s;
	}
	
public String transformToSMVSyntax_V(String s){
		
		//wenn es ein W enthält, dann muß der String noch weiter verändert werden, da NuSMV kein W unterstützt
		
			s = s.replace("!", "->");
			s = s.replace("P", "(\"+p+\")");
			s = s.replace("Q", "(\"+q+\")");
			s = s.replace("R", "(\"+r+\")");
			s = s.replace("S", "(\"+s+\")");
			s = s.replace("T", "(\"+t+\")");
			s = s.replace("Z", "(\"+z+\")");
			//s = s.replace("[", "(");
			//s = s.replace("]", ")");
			s = s.replace("^", "&");
			s = s.replace("¬", "!");
			s = s.replace("_", "|");
			s = s.replace("EF", "EBF 0..");
			s = s.replace("EG", "EBG 0..");
			s = s.replace("AF", "ABF 0..");
			s = s.replace("AG", "ABG 0..");
			s = s.replace("U", "BU 0..");
			s = s.replace("c", "\"+c+\"");
			s = s.replace("W", "V");
		
		System.out.println(s);
		return s;
	}
	
public String transformLiteralsToSMVSyntax(String s){		
		//wenn es ein W enthält, dann muß der String noch weiter verändert werden, da NuSMV kein W unterstützt
		
			s = s.replace("P", "(\"+p+\")");
			s = s.replace("Q", "(\"+q+\")");
			s = s.replace("R", "(\"+r+\")");
			s = s.replace("S", "(\"+s+\")");
			s = s.replace("T", "(\"+t+\")");
			s = s.replace("Z", "(\"+z+\")");
			s = s.replace("c", "\"+c+\"");
		System.out.println(s);
		return s;
	}
	

//Und nun die ganzen Funktionen, um die Patterns einzeln nach CTL zu übersetzen
//Kopiere Strings aus PFD hier als String rein (CTL)
public void getPossibleResponse_inCTL(){
	String possResp_Globally = "AG(P ! EF S )";
	String possResp_Before = "A(((P ! E[(¬R ) U (S ^¬R )]) _AG(¬R )) W R )";
	String possResp_After = "A(¬Q W (Q ^ AG (P ! EF(S ))))";
	String possResp_Between = "AG(Q ^¬R ! A[((P ! E[¬R U (S ^¬R )]) _ AG(¬R )) W R ])";
	String possResp_Until = "AG(Q ^ ¬R ! A[(P ! E[¬R U (S ^ ¬R )]) W R ])";
	
	System.out.println("*****************Formulas in CTL of the possible response pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(possResp_Globally);
	translator.transformToSMVSyntax(possResp_Before);
	translator.transformToSMVSyntax(possResp_After);
	translator.transformToSMVSyntax(possResp_Between);
	translator.transformToSMVSyntax(possResp_Until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     with replaced W      *******");
	possResp_Globally 	 = translator.transformToSMVSyntax(possResp_Globally);
	possResp_Before		 = translator.replace_AW_inCTL("((P -> E((!R ) U (S &!R ))) |AG(!R ))", "R");
	possResp_After 		 = translator.replace_AW_inCTL("!Q" , "(Q & AG (P -> EF(S )))");
	  String possResp_Between1 = translator.replace_AW_inCTL("((P -> E(!R U (S &!R ))) | AG(!R ))" , "R");
	possResp_Between 	= "AG(Q &!R -> ("+possResp_Between1+"))";
	  String possResp_Until1 	= translator.replace_AW_inCTL("(P -> E(!R U (S & !R )))" , "R");
	possResp_Until 		 = "AG(Q & !R -> ("+possResp_Until1+"))";
	
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	possResp_Before 	 = translator.transformLiteralsToSMVSyntax(possResp_Before);
	possResp_After 		 = translator.transformLiteralsToSMVSyntax(possResp_After);
	possResp_Between 	 = translator.transformLiteralsToSMVSyntax(possResp_Between);
	possResp_Until 	 	 = translator.transformLiteralsToSMVSyntax(possResp_Until);
	//possResp_Globally 	 = translator.transformToSMVSyntax(possResp_Globally);
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getAbsence_inCTL(){
	String absence_Globally = "AG(¬P )";
	String absence_Before = "A((¬P _ AG(¬R )) W R )";
	String absence_After = "AG(Q!AG(¬P ))";
	String absence_Between = "AG((Q ^¬R )! A((¬P _ AG(¬R )) W R ))";
	String absence_Until = "AG((Q ^¬R )! A(¬P W R ))";
	
	System.out.println("*****************Formulas in CTL of the absence pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(absence_Globally);
	translator.transformToSMVSyntax(absence_Before);
	translator.transformToSMVSyntax(absence_After);
	translator.transformToSMVSyntax(absence_Between);
	translator.transformToSMVSyntax(absence_Until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     Zwischenergebnisse      *******");
	absence_Globally 	 = translator.transformToSMVSyntax(absence_Globally);
	absence_Before		 = translator.replace_AW_inCTL("(!P | AG(!R ))", "R");
	absence_After 		 = translator.transformToSMVSyntax(absence_After);
	  String between1 = translator.replace_AW_inCTL("(!P | AG(!R ))" , "R");
	absence_Between 	= "AG((Q &!R )->("+between1+"))";
	  String until1 	= translator.replace_AW_inCTL("!P" , "R");
	absence_Until 		 = "AG((Q &!R )->("+until1+"))";
	
	System.out.println("********     with replaced W      *******");
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	absence_Globally = translator.transformLiteralsToSMVSyntax(absence_Globally);
	absence_Before 	 = translator.transformLiteralsToSMVSyntax(absence_Before);
	absence_After 	 = translator.transformLiteralsToSMVSyntax(absence_After);
	absence_Between  = translator.transformLiteralsToSMVSyntax(absence_Between);
	absence_Until 	 = translator.transformLiteralsToSMVSyntax(absence_Until);
	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getExistence_inCTL(){
	String globally = "AF(P )";
	String before = "A(¬R W (P ^¬R ))";
	String after = "A(¬Q W (Q ^ AF(P )))";
	String between = "AG((Q ^¬R ) ! A(¬R W (P ^¬R )))";
	String until = "AG((Q ^¬R ) ! A(¬R U (P ^¬R )))";
	
	System.out.println("*****************Formulas in CTL of the absence pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     Zwischenergebnisse      *******");
	globally 	 = translator.transformToSMVSyntax(globally);
	before		 = translator.replace_AW_inCTL("!R", "(P &!R )");
	after 		 = translator.replace_AW_inCTL("!Q", "(Q & AF(P ))");
	  String between1 = translator.replace_AW_inCTL("!R" , "(P &!R )");
	between 	= "AG((Q &!R ) ->("+between1+"))";
	  //String until1 	= translator.replace_AW_inCTL("!P" , "R");
	until 		 = translator.transformToSMVSyntax(until);
	
	System.out.println("********     with replaced W      *******");
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	globally = translator.transformLiteralsToSMVSyntax(globally);
	before 	 = translator.transformLiteralsToSMVSyntax(before);
	after 	 = translator.transformLiteralsToSMVSyntax(after);
	between  = translator.transformLiteralsToSMVSyntax(between);
	until 	 = translator.transformLiteralsToSMVSyntax(until);
	
}
	
//Kopiere Strings aus PFD hier als String rein (CTL)
public void getBndExistence_inCTL(){
	String globally = "¬EF(¬P ^ EX(P ^ EF(¬P ^ EX(P ^ EF(¬P ^ EX(P ))))))";
	String before = "¬E(¬R U (¬P ^¬R ^ EX(P ^ E(¬R U (¬P ^¬R ^ EX(P ^ E(¬R U (¬P ^¬R ^ EX(P ^¬R )))))))))";
	String after = "¬E(¬Q U (Q ^ EF(¬P ^ EX(P ^ EF (¬P ^ EX(P ^ EF(¬P ^ EX(P ))))))))";
	String between = "AG(Q ! ¬E(¬R U (¬P ^¬R ^EX(P ^ E(¬R U (¬P ^¬R ^EX(P ^ E(¬R U (¬P ^¬R ^EX(P ^¬R ^EF(R )))))))))))";
	String until = "AG(Q ! ¬E(¬R U (¬P ^¬R ^EX(P ^ E(¬R U (¬P ^¬R ^EX(P ^ E(¬R U (¬P ^¬R ^EX(P ^¬R ))))))))))";
	
	System.out.println("*****************Formulas in CTL of the absence pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Keine W vorhanden --> einfacher
	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getUniversality_inCTL(){
	String globally = "AG(P )";
	String before = "A((P _AG(¬R ))W R )";
	String after = "AG(Q ! AG(P ))";
	String between = "AG((Q ^¬R )! A((P _AG(¬R )) W R ))";
	String until = "AG((Q ^¬R )! A(P W R ))";
	
	System.out.println("*****************Formulas in CTL of the absence pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     Zwischenergebnisse      *******");
	globally 	 = translator.transformToSMVSyntax(globally);
	before		 = translator.replace_AW_inCTL("(P |AG(!R ))", "R");
	after 		 = translator.transformToSMVSyntax(after);
	  String between1 = translator.replace_AW_inCTL("(P |AG(!R ))" , "R");
	between 	= "AG((Q &!R )-> ("+between1+"))";
	  String until1 	= translator.replace_AW_inCTL("P" , "R");
	until 		 = "AG((Q &!R )-> ("+until1+"))";
	
	System.out.println("********     with replaced W      *******");
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	globally = translator.transformLiteralsToSMVSyntax(globally);
	before 	 = translator.transformLiteralsToSMVSyntax(before);
	after 	 = translator.transformLiteralsToSMVSyntax(after);
	between  = translator.transformLiteralsToSMVSyntax(between);
	until 	 = translator.transformLiteralsToSMVSyntax(until);
	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getPrecedence_inCTL(){
	String globally = "A(¬P W S )";
	String before = "A((¬P _AG(¬R )) W (S _ R ))";
	String after = "A(¬Q W (Q ^ A(¬P W S )))";
	String between = "AG((Q ^¬R )! A((¬P _ AG(¬R )) W (S _R )))";
	String until = "AG((Q ^¬R )! A(¬P W (S _R )))";
	
	System.out.println("*****************Formulas in CTL of the absence pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     Zwischenergebnisse      *******");
	globally 	 = translator.replace_AW_inCTL("!P", "S");
	before		 = translator.replace_AW_inCTL("(!P |AG(!R ))", "(S | R )");
	  String after1 		 = translator.replace_AW_inCTL("!P", "S");
	  after1 = "A(!Q W (Q & " +after1+"))";
	  System.out.println(after1);
	after = translator.replace_AW_inCTL("!Q ", "(Q & !E(!(S) U (!(!P) & !(S))))");
	  String between1 = translator.replace_AW_inCTL("(!P | AG(!R ))" , "(S |R )");
	between 	= "AG((Q &!R )-> ("+between1+"))";
	  String until1 	= translator.replace_AW_inCTL("!P" , "(S |R )");
	until 		 = "AG((Q &!R )-> ("+until1+"))";
	
	System.out.println("********     with replaced W      *******");
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	globally = translator.transformLiteralsToSMVSyntax(globally);
	before 	 = translator.transformLiteralsToSMVSyntax(before);
	after 	 = translator.transformLiteralsToSMVSyntax(after);
	between  = translator.transformLiteralsToSMVSyntax(between);
	until 	 = translator.transformLiteralsToSMVSyntax(until);
	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getResponse_inCTL(){
	String globally = "AG(P! AF(S ))";
	String before = "A(((P ! A(¬R U (S ^¬R )))_ AG(¬R )) W R )";
	String after = "A(¬Q W(Q ^AG(P!AF(S ))))";
	String between = "AG((Q ^¬R )!A(((P!A(¬R U (S ^¬R ))) _ AG(¬R ))W R ))";
	String until = "AG((Q ^¬R )!A((P!A(¬R U (S ^¬R ))) W R ))";
	
	System.out.println("*****************Formulas in CTL of the absence pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     Zwischenergebnisse      *******");
	globally 	 = translator.transformToSMVSyntax(globally);
	before		 = translator.replace_AW_inCTL("((P -> A(!R U (S &!R )))| AG(!R ))", "R");
	  //String after1 		 = translator.replace_AW_inCTL("!P", "S");
	  //after1 = "A(!Q W (Q & " +after1+"))";
	  //System.out.println(after1);
	after = translator.replace_AW_inCTL("!Q ", "(Q &AG(P->AF(S )))");
	  String between1 = translator.replace_AW_inCTL("((P->A(!R U (S &!R ))) | AG(!R ))" , "R");
	between 	= "AG((Q &!R )-> ("+between1+"))";
	  String until1 	= translator.replace_AW_inCTL("(P->A(!R U (S &!R )))" , "R");
	until 		 = "AG((Q &!R )-> ("+until1+"))";
	
	System.out.println("********     with replaced W      *******");
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	globally = translator.transformLiteralsToSMVSyntax(globally);
	before 	 = translator.transformLiteralsToSMVSyntax(before);
	after 	 = translator.transformLiteralsToSMVSyntax(after);
	between  = translator.transformLiteralsToSMVSyntax(between);
	until 	 = translator.transformLiteralsToSMVSyntax(until);
	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getPrecedenceChain21_inCTL(){
	String globally = "¬E(¬S U P )^¬E(¬P U (S ^¬P ^EX(E(¬T U (P ^¬T )))))";
	String before = "¬E((¬S ^¬R ) U (P ^¬R ))^¬E((¬P ^¬R ) U (S ^¬P ^¬R ^EX(E((¬T ^¬R ) U (P ^¬T ^¬R )))))";
	String after = "¬E(¬Q U (Q ^E(¬S U P )^E(¬P U (S ^¬P ^EX(E(¬T U (P ^¬T )))))))";
	String between = "AG(Q! ¬E((¬S ^¬R ) U (P ^¬R ^EF(R )))^¬E((¬P ^¬R ) U (S ^¬P ^¬R ^EX(E((¬T ^¬R ) U (P ^¬T ^¬R ^EF(R )))))))";
	String until = "AG(Q! ¬E((¬S ^¬R ) U (P ^¬R )) ^¬E((¬P ^¬R ) U (S ^¬P ^¬R ^ EX(E((¬T ^¬R ) U (P ^¬T ^¬R ))))))";
	
	System.out.println("*****************Formulas in CTL of the precedenceChainPattern 21 pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Keine W vorhanden --> einfacher
	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getPrecedenceChain12_inCTL(){
	String globally = "¬E(¬P U (S ^¬P ^EX(EF(T ))))";
	String before = "¬E((¬P ^¬R ) U (S ^¬P ^¬R ^EX(E(¬R U (T ^¬R )))))";
	String after = "¬E(¬Q U (Q ^E(¬P U (S ^¬P ^EX(EF(T ))))))";
	String between = "AG(Q! ¬E((¬P ^¬R ) U (S ^¬P ^¬R ^EX(E(¬R U (T ^¬R ^EF(R )))))))";
	String until = "AG(Q! ¬E((¬P ^¬R ) U (S ^¬P ^¬R ^EX(E(¬R U (T ^¬R ))))))";
	
	System.out.println("*****************Formulas in CTL of the precedenceChainPattern 12 pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Keine W vorhanden --> einfacher	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getResponseChain21_inCTL(){
	String globally = "¬EF(S ^ EX(EF(T ^ EG(¬P ))))";
	String before = "¬E(¬R U (S ^¬R ^ EX(E(¬R U (T ^¬R ^E(¬P U R ))))))";
	String after = "¬E(¬Q U (Q ^EF(S ^ EX(EF(T ^ EG(¬P ))))))";
	String between = "AG(Q! ¬E(¬R U (S ^¬R ^ EX(E(¬R U (T ^¬R ^E(¬P U R )))))))";
	String until = "AG(Q! ¬E(¬R U (S ^¬R ^ EX(E(¬R U (T ^¬R ^ (E(¬P U R ) _ EG(¬P ^¬R ))))))))";
	
	System.out.println("*****************Formulas in CTL of the responseChainPattern 21 pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Keine W vorhanden --> einfacher	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getResponseChain12_inCTL(){
	String globally = "AG(P ! AF(S ^AX(AF(T ))))";
	String before = "¬E(¬R U (P ^¬R ^(E(¬S U R ) _ E(¬R U(S ^¬R ^ EX(E(¬T U R )))))))";
	String after = "¬E(¬Q U (Q ^EF(P ^(EG(¬S ) _ EF(S ^ EX(EG(¬T )))))))";
	String between = "AG(Q! ¬E(¬R U (P ^¬R ^(E(¬S U R ) _ E(¬R U(S ^¬R ^ EX(E(¬T U R ))))))))";
	String until = "AG(Q! ¬E(¬R U (P ^¬R ^(E(¬S U R ) _ EG(¬S ^¬R ) _ E(¬R U(S ^¬R ^ EX(E(¬T U R ) _ EG(¬T ^¬R ))))))))";
	
	System.out.println("*****************Formulas in CTL of the responseChainPattern 12 pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Keine W vorhanden --> einfacher	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getConstrainedChain_inCTL(){
	String globally = "AG(P ! AF(S ^¬Z ^AX(A(¬Z U T ))))";
	String before = "¬E(¬R U (P ^¬R ^(E(¬S U R ) _ E(¬R U(S ^¬R ^ (E(¬T U Z )_EX(E(¬T U R ))))))))";
	String after = "¬E(¬Q U (Q ^EF(P ^EG(¬S ) _ EF(S ^(E(¬T U Z )_EX(EG(¬T )))))))";
	String between = "AG(Q! ¬E(¬R U (P ^¬R ^(E(¬S U R ) _ E(¬R U(S ^¬R ^ (E(¬T U Z )_EX(E(¬T U R )))))))))";
	String until = "AG(Q! ¬E(¬R U (P ^¬R ^(E(¬S U R )_ EG(¬S ^¬R ) _ E(¬R U(S ^¬R ^ (E(¬T U Z )_EX(E(¬T U R )_ EG(¬T ^¬R )))))))))";
	
	System.out.println("*****************Formulas in CTL of the constrainedChainPattern  pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Keine W vorhanden --> einfacher	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getInvariant_inCTL(){
	String absence_Globally = "AG(P!S )";
	String absence_Before = "A(((P!S ) _ AG(¬R )) W R )";
	String absence_After = "AG(Q!AG(P!S ))";
	String absence_Between = "AG((Q ^¬R )! A(((P!S ) _ AG(¬R )) W R ))";
	String absence_Until = "AG((Q ^¬R )! A((P!S ) W R ))";
	
	System.out.println("*****************Formulas in CTL of the invariant pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(absence_Globally);
	translator.transformToSMVSyntax(absence_Before);
	translator.transformToSMVSyntax(absence_After);
	translator.transformToSMVSyntax(absence_Between);
	translator.transformToSMVSyntax(absence_Until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     Zwischenergebnisse      *******");
	absence_Globally 	 = translator.transformToSMVSyntax(absence_Globally);
	absence_Before		 = translator.replace_AW_inCTL("((P->S ) | AG(!R ))", "R");
	absence_After 		 = translator.transformToSMVSyntax(absence_After);
	  String between1 = translator.replace_AW_inCTL("((P->S ) | AG(!R ))" , "R");
	absence_Between 	= "AG((Q &!R )->("+between1+"))";
	  String until1 	= translator.replace_AW_inCTL("(P->S )" , "R");
	absence_Until 		 = "AG((Q &!R )->("+until1+"))";
	
	System.out.println("********     with replaced W      *******");
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	absence_Globally = translator.transformLiteralsToSMVSyntax(absence_Globally);
	absence_Before 	 = translator.transformLiteralsToSMVSyntax(absence_Before);
	absence_After 	 = translator.transformLiteralsToSMVSyntax(absence_After);
	absence_Between  = translator.transformLiteralsToSMVSyntax(absence_Between);
	absence_Until 	 = translator.transformLiteralsToSMVSyntax(absence_Until);
	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getPossBoundedResp_inTCTL(){
	String globally = "AG(P! EFc S )";
	String before = "A[((P ! E[¬R Uc(S ^ ¬R )]) _ AG(¬R )) W R ]";
	String after = "A(¬Q W (Q ^ AG (P ! EFc(S ))))";
	String between = "AG(Q ^ ¬R ! A[((P ! E[¬R Uc(S ^ ¬R )]) _ AG(¬R )) W R ])";
	String until = "AG(Q ^ ¬R ! A[(P ! E[¬R Uc(S ^ ¬R )]) W R ])";
	
	System.out.println("*****************Formulas in TCTL of the possible boundedResponse pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     Zwischenergebnisse      *******");
	globally 	 = translator.transformToSMVSyntax(globally);
	before	 = translator.replace_AW_inCTL("((P -> E[!R BU 0..c(S & !R )]) | AG(!R ))", "R");
	  //String after1 		 = translator.replace_AW_inCTL("!P", "S");
	  //after1 = "A(!Q W (Q & " +after1+"))";
	  //System.out.println(after1);
	after = translator.replace_AW_inCTL("!Q ", "(Q & AG (P -> EBF 0..c(S )))");
	  String between1 = translator.replace_AW_inCTL("((P -> E[!R BU 0..c(S & !R )]) | AG(!R ))" , "R");
	between 	= "AG(Q & !R -> ("+between1+"))";
	  String until1 	= translator.replace_AW_inCTL("(P -> E[!R BU 0..c(S & !R )])" , "R");
	until 		 = "AG(Q & !R -> ("+until1+"))";
	
	System.out.println("********     with replaced W      *******");
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	globally = translator.transformLiteralsToSMVSyntax(globally);
	before 	 = translator.transformLiteralsToSMVSyntax(before);
	after 	 = translator.transformLiteralsToSMVSyntax(after);
	between  = translator.transformLiteralsToSMVSyntax(between);
	until 	 = translator.transformLiteralsToSMVSyntax(until);
	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getPossBoundedInv_inTCTL(){
	String globally = "AG(P! EGc S )";
	String before = "A((P ! EGc(¬R ^ S ) _ AG(¬R )) W R )";
	String after = "A(¬Q W (Q ^ AG (P ! EGc(S )))";
	String between = "AG(Q ^ ¬R ! A[((P ! EGc(S ^ ¬R )) _ AG(¬R )) W R ])";
	String until = "AG(Q ^ ¬R ! A[(P ! EGc(S ^ ¬R )) W R ])";
	
	System.out.println("*****************Formulas in TCTL of the possible bounded Invariance pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     Zwischenergebnisse      *******");
	globally 	 = translator.transformToSMVSyntax(globally);
	before	 = translator.replace_AW_inCTL("(P -> EBG 0..c(!R & S ) | AG(!R ))", "R");
	  //String after1 		 = translator.replace_AW_inCTL("!P", "S");
	  //after1 = "A(!Q W (Q & " +after1+"))";
	  //System.out.println(after1);
	after = translator.replace_AW_inCTL("!Q ", "(Q & AG (P -> EBG 0..c(S ))");
	  String between1 = translator.replace_AW_inCTL("((P -> EBG 0..c(S & !R )) | AG(!R ))" , "R");
	between 	= "AG(Q & !R -> ("+between1+"))";
	  String until1 	= translator.replace_AW_inCTL("(P -> EBG 0..c(S & !R ))" , "R");
	until 		 = "AG(Q & !R -> ("+until1+"))";
	
	System.out.println("********     with replaced W      *******");
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	globally = translator.transformLiteralsToSMVSyntax(globally);
	before 	 = translator.transformLiteralsToSMVSyntax(before);
	after 	 = translator.transformLiteralsToSMVSyntax(after);
	between  = translator.transformLiteralsToSMVSyntax(between);
	until 	 = translator.transformLiteralsToSMVSyntax(until);
	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getBoundedInv_inTCTL(){
	String globally = "AG(P!AGc(S ))";
	String before = "A((P!AGc((S ^¬R )_ AG(¬R ))) W R)";
	String after = "AG(Q! AG(P!AGc(S )))";
	String between = "AG((Q ^¬R )! A((P!AGc((S ^¬R )_ AG(¬R ))) W R ))";
	String until = "AG((Q ^¬R )! A((P!AGc(S ^¬R )) W R ))";
	
	System.out.println("*****************Formulas in TCTL of the bounded Invariance pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     Zwischenergebnisse      *******");
	globally 	 = translator.transformToSMVSyntax(globally);
	before	 = translator.replace_AW_inCTL("(P->ABG 0..c((S &!R )| AG(!R )))", "R");
	  //String after1 		 = translator.replace_AW_inCTL("!P", "S");
	  //after1 = "A(!Q W (Q & " +after1+"))";
	  //System.out.println(after1);
	after = translator.transformToSMVSyntax(after);
	  String between1 = translator.replace_AW_inCTL("(P->ABG 0..c((S &!R )| AG(!R )))" , "R");
	between 	= "AG(Q & !R -> ("+between1+"))";
	  String until1 	= translator.replace_AW_inCTL("(P->ABG 0..c(S &!R ))" , "R");
	until 		 = "AG(Q & !R -> ("+until1+"))";
	
	System.out.println("********     with replaced W      *******");
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	globally = translator.transformLiteralsToSMVSyntax(globally);
	before 	 = translator.transformLiteralsToSMVSyntax(before);
	after 	 = translator.transformLiteralsToSMVSyntax(after);
	between  = translator.transformLiteralsToSMVSyntax(between);
	until 	 = translator.transformLiteralsToSMVSyntax(until);
	
}

//Kopiere Strings aus PFD hier als String rein (CTL)
public void getBoundedResp_inTCTL(){
	String globally = "AG(P ! AFc(S ))";
	String before = "A((P ! (A(¬R Uc(S ^¬R )) _ AG(¬R ))) W R )";
	String after = "AG(Q!AG(P ! AFc(S )))";
	String between = "AG((Q ^¬R )! A(((P ! ((A(¬R Uc(S ^¬R ))))) _ AG(¬R )) W R ))";
	String until = "AG((Q ^¬R )! A((P ! A(¬R Uc(S ^¬R ))) W R ))";
	
	System.out.println("*****************Formulas in TCTL of the boundedResponse pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     Zwischenergebnisse      *******");
	globally 	 = translator.transformToSMVSyntax(globally);
	before	 = translator.replace_AW_inCTL("(P -> (A[!R BU 0..c(S &!R )] | AG(!R )))", "R");
	  //String after1 		 = translator.replace_AW_inCTL("!P", "S");
	  //after1 = "A(!Q W (Q & " +after1+"))";
	  //System.out.println(after1);
	after = translator.transformToSMVSyntax(after);;
	  String between1 = translator.replace_AW_inCTL("((P -> (A[!R BU 0..c(S &!R )])) | AG(!R ))" , "R");
	between 	= "AG((Q &!R )-> ("+between1+"))";
	  String until1 	= translator.replace_AW_inCTL("(P -> A[!R BU 0..c(S &!R )])" , "R");
	until 		 = "AG((Q &!R )-> ("+until1+"))";
	
	System.out.println("********     with replaced W      *******");
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	globally = translator.transformLiteralsToSMVSyntax(globally);
	before 	 = translator.transformLiteralsToSMVSyntax(before);
	after 	 = translator.transformLiteralsToSMVSyntax(after);
	between  = translator.transformLiteralsToSMVSyntax(between);
	until 	 = translator.transformLiteralsToSMVSyntax(until);
	
}

//Kopiere Strings aus PFD hier als String rein (TCTL)
public void getPeriodic_inTCTL(){
	String globally = "AG(AFc(P ))";
	String before = "A(((AFc(P _R _ AG(¬R ))))W R )";
	String after = "AG(Q! AG(AFc(P )))";
	String between = "AG((Q ^¬R )!A((AFc(P _R _ AG(¬R ))) W R ))";
	String until = "AG((Q ^¬R )!A(AFc(P _R ) W R ))";
	
	System.out.println("*****************Formulas in TCTL of the bounded reccurrence(periodic) pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     Zwischenergebnisse      *******");
	globally 	 = translator.transformToSMVSyntax(globally);
	before	 = translator.replace_AW_inCTL("(ABF 0..c(P |R | AG(!R )))", "R");
	  //String after1 		 = translator.replace_AW_inCTL("!P", "S");
	  //after1 = "A(!Q W (Q & " +after1+"))";
	  //System.out.println(after1);
	after = translator.transformToSMVSyntax(after);;
	  String between1 = translator.replace_AW_inCTL("(ABF 0..c(P |R | AG(!R )))" , "R");
	between 	= "AG((Q &!R )-> ("+between1+"))";
	  String until1 	= translator.replace_AW_inCTL("ABF 0..c(P |R )" , "R");
	until 		 = "AG((Q &!R )-> ("+until1+"))";
	
	System.out.println("********     with replaced W      *******");
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	globally = translator.transformLiteralsToSMVSyntax(globally);
	before 	 = translator.transformLiteralsToSMVSyntax(before);
	after 	 = translator.transformLiteralsToSMVSyntax(after);
	between  = translator.transformLiteralsToSMVSyntax(between);
	until 	 = translator.transformLiteralsToSMVSyntax(until);
	
}

//Kopiere Strings aus PFD hier als String rein (TCTL)
public void getMinDuration_inTCTL(){
	String globally = "AG(P _ A(¬P W AGc(P )))";
	String before = "A((P _ A(¬P W (AGc((P ^¬R ) _ AG(¬R )) _ R )) _ AG(¬R )) W R )";
	String after = "AG(Q ! AG(P _ A(¬P W AGc(P ))))";
	String between = "AG((Q ^¬R )!A((P _ A(¬P W (AGc((P ^¬R ) _ AG(¬R )) _ R )) _ AG(¬R )) W R ))";
	String until = "AG((Q ^¬R )! (A(P _ A(¬P W (AGc(P ^¬R )) _ R ) W R )))";
	
	System.out.println("*****************Formulas in TCTL of the minimum duration pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     Zwischenergebnisse      *******");
	  String globally1 	 = translator.replace_AW_inCTL("!P", "ABG 0..c(P )");
	globally = "AG(P | "+globally1+")";
	String before1	 = translator.replace_AW_inCTL("(P | A(!P W (ABG 0..c((P &!R ) | AG(!R )) | R )) | AG(!R ))", "R");
	  System.out.println("****before: "+before1);
	  before1 = translator.replace_AW_inCTL("!P", "(ABG 0..c((P &!R ) | AG(!R )) | R )");
	  before = "!E[!(R) U (!((P | " + before1+"| AG(!R ))) & !(R))]";
	  
	  String after1 		 = translator.replace_AW_inCTL("!P", "ABG 0..c(P )");
	after = "AG(Q -> AG(P |" +after1+"))";
	  String between1 = translator.replace_AW_inCTL("(P | A(!P W (ABG 0..c((P &!R ) | AG(!R )) | R )) | AG(!R ))" , "R");
	between 	= "AG((Q &!R )-> ("+between1+"))";
	System.out.println("*******between: "+between);
	between1 = translator.replace_AW_inCTL("!P", "(ABG 0..c((P &!R ) | AG(!R )) | R )");
	between = "AG((Q &!R )-> (!E[!(R) U (!((P | "+between1+" | AG(!R ))) & !(R))]))";
	
	  String until1 	= translator.replace_AW_inCTL("(P | A(!P W (ABG 0..c(P &!R )) | R )" , "R");
	until 		 = "AG((Q &!R )-> ("+until1+"))";
	System.out.println("*******until: "+until);
	until1 = translator.replace_AW_inCTL("!P", "(ABG 0..c(P &!R ))");
	until = "AG((Q &!R )-> (!E[!(R) U (!((P |"+until1+" | R )) & !(R))]))";
	
	System.out.println("********     with replaced W      *******");
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	globally = translator.transformLiteralsToSMVSyntax(globally);
	before 	 = translator.transformLiteralsToSMVSyntax(before);
	after 	 = translator.transformLiteralsToSMVSyntax(after);
	between  = translator.transformLiteralsToSMVSyntax(between);
	until 	 = translator.transformLiteralsToSMVSyntax(until);
	
}

//Kopiere Strings aus PFD hier als String rein (TCTL)
public void getMaxDuration_inTCTL(){
	String globally = "AG(P _ A(¬P W (P^ AFc(¬P ))))";
	String before = "A((P _ A(¬P W ((P^ AFc(¬P _R _AG(¬R ))) _R _AG(¬R ))) _ AG(¬R )) W R )";
	String after = "AG(Q!AG(P _ A(¬P W (P^ AFc(¬P )))))";
	String between = "AG((Q ^¬R )!A((P _ A(¬P W ((P^ AFc(¬P _R _AG(¬R ))) _R _AG(¬R ))) _ AG(¬R )) W R ))";
	String until = "AG((Q ^¬R )!(A(P _ A(¬P W ((P^ AFc(¬P _R )) _R )) W R )))";
	
	System.out.println("*****************Formulas in TCTL of the maximum duration pattern **************");
	ToNuSMV translator = new ToNuSMV();
	translator.transformToSMVSyntax(globally);
	translator.transformToSMVSyntax(before);
	translator.transformToSMVSyntax(after);
	translator.transformToSMVSyntax(between);
	translator.transformToSMVSyntax(until);
	
	//Weil man mit regulären Ausdrücken nicht rausfindet, welche schließende Klammer zu welcher öffneneden gehört
	//muß man per Hand die passenden Ausdrücke zusammensammeln - Bißchen doof, aber immerhin
	System.out.println("********     Zwischenergebnisse      *******");
	  String globally1 	 = translator.replace_AW_inCTL("!P", "(P& ABF 0..c(!P ))");
	globally = "AG(P | "+globally1+")";
	String before1	 = translator.replace_AW_inCTL("!P", "((P& ABF 0..c(!P |R |AG(!R ))) |R |AG(!R ))");
	before ="A((P | "+before1+" | AG(!R )) W R )";
	  System.out.println("****before: "+before);
	  before = translator.replace_AW_inCTL("(P | !E[!(((P& ABF 0..c(!P |R |AG(!R ))) |R |AG(!R ))) U (!(!P) & !(((P& ABF 0..c(!P |R |AG(!R ))) |R |AG(!R ))))] | AG(!R ))", "R");
	  
	  String after1 		 = translator.replace_AW_inCTL("!P", "(P& ABF 0..c(!P ))");
	after = "AG(Q->AG(P |" +after1+"))";
	  String between1 = translator.replace_AW_inCTL("(P | A(!P W ((P& ABF 0..c(!P |R |AG(!R ))) |R |AG(!R ))) | AG(!R ))" , "R");
	between 	= "AG((Q &!R )-> ("+between1+"))";
	System.out.println("*******between: "+between);
	between1 = translator.replace_AW_inCTL("!P", "((P& ABF 0..c(!P |R |AG(!R ))) |R |AG(!R ))");
	between = "AG((Q &!R )-> (!E[!(R) U (!((P | "+between1+" | AG(!R ))) & !(R))]))";
	
	  String until1 	= translator.replace_AW_inCTL("!P" , "((P& ABF 0..c(!P |R )) |R )");
	until 		 = "AG((Q &!R )->(A(P | "+until1+" W R )))";
	System.out.println("*******until: "+until);
	until1 = translator.replace_AW_inCTL("(P | !E[!((P& ABF 0..c(!P |R )) |R ) U (!(!P) & !((P& ABF 0..c(!P |R )) |R ))])", "R");
	until = "AG((Q &!R )-> "+until1+" )";
	
	System.out.println("********     with replaced W      *******");
	//Nachdem das W ersetzt ist: Und nun noch in NuSMV-Syntax übersetzen
	globally = translator.transformLiteralsToSMVSyntax(globally);
	before 	 = translator.transformLiteralsToSMVSyntax(before);
	after 	 = translator.transformLiteralsToSMVSyntax(after);
	between  = translator.transformLiteralsToSMVSyntax(between);
	until 	 = translator.transformLiteralsToSMVSyntax(until);
	
}
	
}
