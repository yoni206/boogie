﻿using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
    public class CivlVCGeneration
    {
        public static void Transform(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker)
        {
            Program program = linearTypeChecker.program;

            // Store the original declarations of yielding procedures, which will be removed after desugaring below.
            var origProc = program.TopLevelDeclarations.OfType<Procedure>().Where(p => civlTypeChecker.procToYieldingProc.ContainsKey(p));
            var origImpl = program.TopLevelDeclarations.OfType<Implementation>().Where(i => civlTypeChecker.procToYieldingProc.ContainsKey(i.Proc));
            List<Declaration> originalDecls = Enumerable.Union<Declaration>(origProc, origImpl).ToList();

            // Commutativity checks
            List<Declaration> decls = new List<Declaration>();
            if (!CommandLineOptions.Clo.TrustAtomicityTypes)
            {
                MoverCheck.AddCheckers(linearTypeChecker, civlTypeChecker, decls);
            }

            // Desugaring of yielding procedures
            YieldingProcChecker.AddCheckers(linearTypeChecker, civlTypeChecker, decls);

            // Linear type checks
            LinearTypeChecker.AddCheckers(linearTypeChecker, civlTypeChecker, decls);

            // Remove original declarations and add new checkers generated above
            program.RemoveTopLevelDeclarations(x => originalDecls.Contains(x));
            program.AddTopLevelDeclarations(decls);

            civlTypeChecker.SubstituteBackwardAssignments();

            foreach (AtomicAction atomicAction in civlTypeChecker.procToAtomicAction.Values)
            {
                program.RemoveTopLevelDeclaration(atomicAction.proc);
                program.RemoveTopLevelDeclaration(atomicAction.impl);
            }
        }
    }
}
