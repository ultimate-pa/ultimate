/*
 * 6.4.2017 DD
 * 
 * This program triggers the following assertion error (with Taipan and with FixedPreferences Z3, FP/BP, TwoTrack)
 *
 * java.lang.AssertionError: unreachable return
 *    at de.uni_freiburg.informatik.ultimate.automata.nestedword.DownStateConsistencyCheck.checkIfEachDownStateIsJustified(DownStateConsistencyCheck.java:147)
 *    at de.uni_freiburg.informatik.ultimate.automata.nestedword.DownStateConsistencyCheck.consistentForState(DownStateConsistencyCheck.java:125)
 *    at de.uni_freiburg.informatik.ultimate.automata.nestedword.DownStateConsistencyCheck.consistentForAll(DownStateConsistencyCheck.java:105)
 *    at de.uni_freiburg.informatik.ultimate.automata.nestedword.DownStateConsistencyCheck.<init>(DownStateConsistencyCheck.java:75)
 *    at de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDeckerAutomatonFilteredStates.<init>(DoubleDeckerAutomatonFilteredStates.java:89)
 *    at de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference.removeDeadEnds(Difference.java:206)
 *    at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop.refineWithGivenAutomaton(BasicCegarLoop.java:471)
 *    at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop.refineAbstraction(BasicCegarLoop.java:393)
 *    at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.iterate(AbstractCegarLoop.java:377)
 *    at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.iterate(TraceAbstractionStarter.java:280)
 *    at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.runCegarLoops(TraceAbstractionStarter.java:133)
 *    at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.<init>(TraceAbstractionStarter.java:103)
 *    at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionObserver.finish(TraceAbstractionObserver.java:105)
 *    at de.uni_freiburg.informatik.ultimate.core.coreplugin.PluginConnector.runObserver(PluginConnector.java:168)
 *    at de.uni_freiburg.informatik.ultimate.core.coreplugin.PluginConnector.runTool(PluginConnector.java:151)
 *    at de.uni_freiburg.informatik.ultimate.core.coreplugin.PluginConnector.run(PluginConnector.java:128)
 *    at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.executePluginConnector(ToolchainWalker.java:232)
 *    at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.processPlugin(ToolchainWalker.java:226)
 *    at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.walkUnprotected(ToolchainWalker.java:142)
 *    at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.walk(ToolchainWalker.java:104)
 *    at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainManager$Toolchain.processToolchain(ToolchainManager.java:283)
 *    at de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob.rerunToolchain(DefaultToolchainJob.java:173)
 *    at de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob.run(BasicToolchainJob.java:131)
 *    at org.eclipse.core.internal.jobs.Worker.run(Worker.java:55)
 *     
 */

var ~__ste_email_to0 : int;

procedure ULTIMATE.start() returns ()
modifies ~__ste_email_to0;
{
    ~__ste_email_to0 := 0;
    call main();
}

procedure findPublicKey(#in~handle : int, #in~userid : int) returns (){
    var ~handle : int;
    var ~userid : int;

    ~handle := #in~handle;
    ~userid := #in~userid;
    if (~handle != 0) {
    }
}

procedure bobToRjh() returns ()
modifies ~__ste_email_to0;
{
    call sendEmail(0, 0);
    call outgoing(0, 0);
}

procedure main() returns ()
modifies ~__ste_email_to0;
{
    call test();
}

procedure mail(#in~client : int, #in~msg : int) returns ()
modifies ~__ste_email_to0;
{
    var #t~ret0 : int;
    var ~client : int;
    var ~msg : int;
    var ~tmp~11 : int;

    ~client := #in~client;
    ~msg := #in~msg;
    havoc ~tmp~11;
    call #t~ret0 := getEmailTo(0);
    assume -2147483648 <= #t~ret0 && #t~ret0 <= 2147483647;
    ~tmp~11 := #t~ret0;
    havoc #t~ret0;
    call incoming(~tmp~11, 0);
}

procedure outgoing__wrappee__AutoResponder(#in~client : int, #in~msg : int) returns ()
modifies ~__ste_email_to0;
{
    var ~client : int;
    var ~msg : int;

    ~client := #in~client;
    ~msg := #in~msg;
    call mail(0, 0);
}

procedure outgoing(#in~client : int, #in~msg : int) returns ()
modifies ~__ste_email_to0;
{
    var ~client : int;
    var ~msg : int;

    ~client := #in~client;
    ~msg := #in~msg;
    call outgoing__wrappee__AutoResponder(0, 0);
}

procedure incoming__wrappee__Sign(#in~client : int, #in~msg : int) returns ()
modifies ~__ste_email_to0;
{
    var ~client : int;
    var ~msg : int;

    ~client := #in~client;
    ~msg := #in~msg;
    call autoRespond(0, 0);
}

procedure incoming(#in~client : int, #in~msg : int) returns ()
modifies ~__ste_email_to0;
{
    var ~client : int;
    var ~msg : int;

    ~client := #in~client;
    ~msg := #in~msg;
    call verify(~client, 0);
    call incoming__wrappee__Sign(0, 0);
}

procedure sendEmail(#in~sender : int, #in~receiver : int) returns ()
modifies ~__ste_email_to0;
{
    var ~sender : int;
    var ~receiver : int;

    ~sender := #in~sender;
    ~receiver := #in~receiver;
    call outgoing(0, 0);
}


procedure autoRespond(#in~client : int, #in~msg : int) returns ()
modifies ~__ste_email_to0;
{
    var ~client : int;
    var ~msg : int;

    ~client := #in~client;
    ~msg := #in~msg;
    call setEmailTo(0, 0);
}

procedure verify(#in~client : int, #in~msg : int) returns (){
    var ~client : int;
    var ~msg : int;
    var ~__utac__ad__arg1~19 : int;

    ~client := #in~client;
    ~msg := #in~msg;
    havoc ~__utac__ad__arg1~19;
    ~__utac__ad__arg1~19 := ~client;
    call __utac_acc__SignVerify_spec__2(~__utac__ad__arg1~19, 0);
}

procedure getEmailTo(#in~handle : int) returns (#res : int){
    var ~handle : int;
    var ~retValue_acc~20 : int;

    ~handle := #in~handle;
    havoc ~retValue_acc~20;
    ~retValue_acc~20 := ~__ste_email_to0;
    #res := ~retValue_acc~20;
    return;
}

procedure setEmailTo(#in~handle : int, #in~value : int) returns ()
modifies ~__ste_email_to0;
{
    var ~handle : int;
    var ~value : int;

    ~handle := #in~handle;
    ~value := #in~value;
    ~__ste_email_to0 := 1;
}

procedure __utac_acc__SignVerify_spec__2(#in~client : int, #in~msg : int) returns (){
    var ~client : int;
    var ~msg : int;
    var ~pubkey~22 : int;

    ~client := #in~client;
    ~msg := #in~msg;
    havoc ~pubkey~22;
    call findPublicKey(~client, 0);
    if (~pubkey~22 != 0) {
        assert false;
    }
}

procedure test() returns ()
modifies ~__ste_email_to0;
{
    call bobToRjh();
}



