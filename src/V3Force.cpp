// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Covert forceable signals, process force/release
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//  V3Force's Transformations:
//
//  For each forceable net with name "<name>":
//      add 3 extra signals:
//          - <name>__VforceRd: a net with same type as signal
//          - <name>__VforceEn: a var with same type as signal, which is the bitwise force enable
//          - <name>__VforceVl: a var with same type as signal, which is the forced value
//      add an initial statement:
//          initial <name>__VforceEn = 0;
//      add a continuous assignment:
//          assign <name>__VforceRd = <name>__VforceEn ? <name>__VforceVl : <name>;
//      replace all READ references to <name> with a read reference to <name>_VforceRd
//
//  Replace each AstAssignForce with 3 assignments:
//      - <lhs>__VforceEn = 1
//      - <lhs>__VforceVl = <rhs>
//      - <lhs>__VforceRd = <rhs>
//
//  Replace each AstRelease with 1 or 2 assignments:
//      - <lhs>__VforceEn = 0
//      - <lhs>__VforceRd = <lhs> // iff lhs is a net
//
//*************************************************************************
#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Force.h"

#include "V3AstUserAllocator.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Convert force/release statements and signals marked 'forceable'

class ForceConvertVisitor final : public VNVisitor {
    // TYPES
    struct ForceComponentsVar final {
        AstVar* const m_rdVarp;  // New variable to replace read references with
        AstVar* const m_valVarp; // Forced value
        AstVar* const m_enVarp;  // Force enabled signal

        explicit ForceComponentsVar(AstVar* varp)
            : m_rdVarp{new AstVar{varp->fileline(), VVarType::WIRE, varp->name() + "__VforceRd",
                                  varp->dtypep()}}
            , m_valVarp{new AstVar{varp->fileline(), VVarType::VAR, varp->name() + "__VforceVal",
                                   varp->dtypep()}}
            , m_enVarp{new AstVar{varp->fileline(), VVarType::VAR, varp->name() + "__VforceEn",
                                  ( (isRangedDType(varp) ||  VN_IS(varp->dtypeSkipRefp(), UnpackArrayDType)) ? varp->dtypep() : varp->findBitDType())}} {
                                    // i would say that the problem is this checdk more so than anything
            m_rdVarp->addNext(m_enVarp);
            m_rdVarp->addNext(m_valVarp);
            varp->addNextHere(m_rdVarp);

            if (varp->isPrimaryIO()) {
                varp->v3warn(
                    E_UNSUPPORTED,
                    "Unsupported: Force/Release on primary input/output net "
                        << varp->prettyNameQ() << "\n"
                        << varp->warnMore()
                        << "... Suggest assign it to/from a temporary net and force/release that");
            }
        }
    };

    struct ForceComponentsVarScope final {
        AstVarScope* const m_rdVscp;  // New variable to replace read references with
        AstVarScope* const m_enVscp;  // Force enabled signal
        AstVarScope* const m_valVscp;  // Forced value
        explicit ForceComponentsVarScope(AstVarScope* vscp, ForceComponentsVar& fcv)
            : m_rdVscp{new AstVarScope{vscp->fileline(), vscp->scopep(), fcv.m_rdVarp}}
            , m_enVscp{new AstVarScope{vscp->fileline(), vscp->scopep(), fcv.m_enVarp}}
            , m_valVscp{new AstVarScope{vscp->fileline(), vscp->scopep(), fcv.m_valVarp}} {
            m_rdVscp->addNext(m_enVscp);
            m_rdVscp->addNext(m_valVscp);
            vscp->addNextHere(m_rdVscp);

            FileLine* const flp = vscp->fileline();
            // TODO init properly for unpacked case
            {  // Add initialization of the enable signal
                AstVarRef* const lhsp = new AstVarRef{flp, m_enVscp, VAccess::WRITE};
                V3Number zero{m_enVscp, m_enVscp->width()};
                zero.setAllBits0();
                AstNodeExpr* const rhsp = new AstConst{flp, zero};

                AstAssign* assignp;
                if(VN_IS(vscp->varp()->dtypeSkipRefp(), UnpackArrayDType)) {
                  assignp = new AstAssign{flp, new AstArraySel{flp, lhsp, 0}, rhsp->cloneTreePure(false)};
                  for(int idx = 1; idx<VN_CAST(m_enVscp->varp()->dtypeSkipRefp(), UnpackArrayDType)->elementsConst(); idx++) {
                    assignp->addNext(
                        new AstAssign{flp, new AstArraySel{flp, lhsp->cloneTreePure(false), idx}, rhsp->cloneTreePure(false)}
                        );
                  }
                } else {
                  assignp = new AstAssign{flp, lhsp, rhsp};
                }

                AstActive* const activep = new AstActive{
                    flp, "force-init",
                    new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Initial{}}}};

                activep->sensesStorep(activep->sensesp());
                activep->addStmtsp(new AstInitial{flp, assignp});
                vscp->scopep()->addBlocksp(activep);
            }
            {  // Add the combinational override
                AstVarRef* const lhsp = new AstVarRef{flp, m_rdVscp, VAccess::WRITE};
                AstVarRef* const origp = new AstVarRef{flp, vscp, VAccess::READ};
                origp->user2(1);  // Don't replace this read ref with the read signal
                std::vector<AstNodeExpr*> rhsp_vec;

                if(VN_IS(vscp->varp()->dtypeSkipRefp(), UnpackArrayDType)) {
                    v3info("into unpacked area");
                    for(int idx = 0; idx < VN_CAST(m_enVscp->varp()->dtypeSkipRefp(), UnpackArrayDType)->elementsConst(); idx++) {
                      if(isRangedDType(vscp)) {
                        rhsp_vec.push_back(new AstOr{
                            flp,
                            new AstAnd{flp,
                              new AstArraySel{flp, new AstVarRef{flp, m_enVscp, VAccess::READ}, idx},
                              new AstArraySel{flp, new AstVarRef{flp, m_valVscp, VAccess::READ}, idx}
                              },
                            new AstAnd{flp,
                              new AstNot{flp, new AstArraySel{flp, new AstVarRef{flp, m_enVscp, VAccess::READ}, idx}},
                              new AstArraySel{flp, new AstVarRef{flp, vscp, VAccess::READ}, idx}
                              }
                            });
                      } else {
                        rhsp_vec.push_back(new AstCond{
                          flp,                                                 // file line
                          new AstArraySel{flp, new AstVarRef{flp, m_enVscp , VAccess::READ}, idx},// condp
                          new AstArraySel{flp, new AstVarRef{flp, m_valVscp, VAccess::READ}, idx},// thenp
                          new AstArraySel{flp, new AstVarRef{flp, vscp,      VAccess::READ}, idx} // elsep
                        });
                      }
                    }
                } else if (isRangedDType(vscp)) {
                    rhsp_vec.push_back(new AstOr{
                        flp,
                        new AstAnd{flp, new AstVarRef{flp, m_enVscp, VAccess::READ},
                        new AstVarRef{flp, m_valVscp, VAccess::READ}},
                        new AstAnd{flp, new AstNot{flp, new AstVarRef{flp, m_enVscp, VAccess::READ}}, origp}
                        });
                } else {
                  rhsp_vec.push_back(new AstCond{
                      flp,
                      new AstVarRef{flp, m_enVscp , VAccess::READ},
                      new AstVarRef{flp, m_valVscp, VAccess::READ},
                      new AstVarRef{flp, vscp,      VAccess::READ}
                  });
                }

                AstActive* const activep
                    = new AstActive{flp, "force-comb",
                                    new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Combo{}}}};

                activep->sensesStorep(activep->sensesp());

                // TODO need to account for case in which unpack array is of ranged type
                // TODO have generic function that iterates over 
                // TODO example_1_test is failing, why?
                if(VN_IS(vscp->varp()->dtypeSkipRefp(), UnpackArrayDType)) {
                  AstAssignW* const astAssignWp = new AstAssignW{flp, new AstArraySel{flp, new AstVarRef{flp, vscp, VAccess::WRITE}, 0}, rhsp_vec[0]};
                  for(int idx=1; idx < rhsp_vec.size(); idx++) {
                    astAssignWp->addNext(
                        new AstAssignW{
                          flp,
                          new AstArraySel{flp, new AstVarRef{flp, vscp, VAccess::WRITE}, idx},
                          rhsp_vec[idx]
                          });
                  }
                  activep->addStmtsp(astAssignWp);
                } else {
                  v3info("new else");
                  AstAssignW* const astAssignWp = new AstAssignW{flp, new AstVarRef{flp, vscp, VAccess::WRITE}, rhsp_vec[0]};
                  activep->addStmtsp(astAssignWp);
                }
                //activep->addStmtsp(astAssignWInitialp);
                vscp->scopep()->addBlocksp(activep);
            }
        }
    };

    // NODE STATE
    //  AstVar::user1p        -> ForceComponentsVar* instance (via m_forceComponentsVar)
    //  AstVarScope::user1p   -> ForceComponentsVarScope* instance (via m_forceComponentsVarScope)
    //  AstVarRef::user2      -> Flag indicating not to replace reference
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    AstUser1Allocator<AstVar, ForceComponentsVar> m_forceComponentsVar;
    AstUser1Allocator<AstVarScope, ForceComponentsVarScope> m_forceComponentsVarScope;

    // METHODS
    static bool isRangedDType(AstNode* nodep) {
        // If ranged we need a multibit enable to support bit-by-bit part-select forces,
        // otherwise forcing a real or other opaque dtype and need a single bit enable.
        const AstBasicDType* const basicp = nodep->dtypep()->skipRefp()->basicp();
        return basicp && basicp->isRanged();
    }
    const ForceComponentsVarScope& getForceComponents(AstVarScope* vscp) {
        AstVar* const varp = vscp->varp();
        return m_forceComponentsVarScope(vscp, vscp, m_forceComponentsVar(varp, varp));
    }

    // Replace each AstNodeVarRef in the given 'nodep' that writes a variable by transforming the
    // referenced AstVarScope with the given function.
    void transformWritenVarScopes(AstNode* nodep, std::function<AstVarScope*(AstVarScope*)> f) {
        UASSERT_OBJ(nodep->backp(), nodep, "Must have backp, otherwise will be lost if replaced");
        nodep->foreach([&f](AstNodeVarRef* refp) {
            if (refp->access() != VAccess::WRITE) return;
            // TODO: this is not strictly speaking safe for some complicated lvalues, eg.:
            //       'force foo[a(cnt)] = 1;', where 'cnt' is an out parameter, but it will
            //       do for now...
            refp->replaceWith(
                new AstVarRef{refp->fileline(), f(refp->varScopep()), VAccess::WRITE});
            VL_DO_DANGLING(refp->deleteTree(), refp);
        });
    }

    // VISIT methods
    void visit(AstNode* nodep) override { iterateChildren(nodep); }


    void visit(AstAssignForce* nodep) override {
        // The AstAssignForce node will be removed for sure
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        pushDeletep(nodep);

        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const lhsp = nodep->lhsp();  // The LValue we are forcing
        AstNodeExpr* const rhsp = nodep->rhsp();  // The value we are forcing it to
        // Set corresponding enable signals to ones
        V3Number ones{lhsp, isRangedDType(lhsp) ? lhsp->width() : 1};
        ones.setAllBits1();
        AstAssign* const setEnp
            = new AstAssign{flp, lhsp->cloneTreePure(false), new AstConst{rhsp->fileline(), ones}};
        transformWritenVarScopes(setEnp->lhsp(), [this](AstVarScope* vscp) {
            return getForceComponents(vscp).m_enVscp;
        });
        // Set corresponding value signals to the forced value
        AstAssign* const setValp
            = new AstAssign{flp, lhsp->cloneTreePure(false), rhsp->cloneTreePure(false)};
        transformWritenVarScopes(setValp->lhsp(), [this](AstVarScope* vscp) {
            return getForceComponents(vscp).m_valVscp;
        });
        // Set corresponding read signal directly as well, in case something in the same process
        // reads it later
        AstAssign* const setRdp = new AstAssign{flp, lhsp->unlinkFrBack(), rhsp->unlinkFrBack()};
        transformWritenVarScopes(setRdp->lhsp(), [this](AstVarScope* vscp) {
            return getForceComponents(vscp).m_rdVscp;
        });

        setEnp->addNext(setValp);
        setEnp->addNext(setRdp);
        relinker.relink(setEnp);
    }

    void visit(AstRelease* nodep) override {
        // The AstRelease node will be removed for sure
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        pushDeletep(nodep);

        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const lhsp = nodep->lhsp();  // The LValue we are releasing

        // Set corresponding enable signals to zero
        V3Number zero{lhsp, isRangedDType(lhsp) ? lhsp->width() : 1};
        zero.setAllBits0();

        int is_unpacked  = VN_IS(nodep->lhsp()->dtypep()->dtypep()->skipRefp(), UnpackArrayDType);
        int num_elements_unpacked;
        if(is_unpacked) {
          num_elements_unpacked = VN_CAST(nodep->lhsp()->dtypep()->skipRefp(), UnpackArrayDType)->elementsConst();
        }
        v3info("is_unpacked          : " <<  is_unpacked);
        v3info("num_elements_unpacked: " <<  num_elements_unpacked);

        // ----------------------------
        // -<lhs>_VforceEn = 0

        AstAssign* resetEnp;
        if(is_unpacked) { // need thi
          resetEnp = new AstAssign{
              flp,
              new AstArraySel{flp, lhsp->cloneTreePure(false), 0},
              new AstConst{lhsp->fileline(), zero}
            };
          for(int idx=1; idx < num_elements_unpacked; idx++) {
            resetEnp->addNext(new AstAssign{
                flp,
                new AstArraySel{flp, lhsp->cloneTreePure(false), idx},
                new AstConst{lhsp->fileline(), zero}
              });
          }
        } else {
          resetEnp = new AstAssign{flp, lhsp->cloneTreePure(false), new AstConst{lhsp->fileline(), zero}};
        }

        for(AstAssign* astNode = resetEnp; astNode; astNode = VN_CAST(astNode->nextp(), Assign)) {
          transformWritenVarScopes(astNode->lhsp(), [this](AstVarScope* vscp) {
              return getForceComponents(vscp).m_enVscp;
          });
        }

        // ----------------------------
        // IEEE 1800-2017 10.6.2: If this is a net, and not a variable, then reset the read
        // signal directly as well, in case something in the same process reads it later. Also, if
        // it is a variable, and not a net, set the original signal to the forced value, as it
        // needs to retain the forced value until the next procedural update, which might happen on
        // a later eval. Luckily we can do all this in a single assignment.
        FileLine* const fl_nowarn = new FileLine{flp};
        fl_nowarn->warnOff(V3ErrorCode::BLKANDNBLK, true);

        std::vector<AstAssign*> resetRdp_vec;
        AstNodeExpr* astNodeExprp = (VN_IS(lhsp->cloneTreePure(false), ArraySel)) ? VN_CAST(lhsp->unlinkFrBack(), ArraySel)->fromp()->cloneTreePure(false) : lhsp->unlinkFrBack();

        // TODO need to switch between the lhsp ver of this
        resetRdp_vec.push_back(new AstAssign{fl_nowarn, astNodeExprp->cloneTreePure(false), astNodeExprp->cloneTreePure(false)});
        if(is_unpacked) {
          for(int idx=1; idx<num_elements_unpacked; idx++) {
            resetRdp_vec.push_back(new AstAssign{fl_nowarn, astNodeExprp->cloneTreePure(false), astNodeExprp->cloneTreePure(false)});
          }
        }
        v3info("resetRdp_vec.size: " << resetRdp_vec.size());

        int array_sel = 0; // jmc| probably still needed for case of non array sel release (release entire var)
        //for (auto resetRdpIt=resetRdp_vec.begin(); resetRdpIt!=resetRdp_vec.end(); ++resetRdpIt, ++array_sel) {
        for(AstAssign* resetRdp : resetRdp_vec) {
          v3info("iter: " << array_sel);
          v3info("at least got past this - " << array_sel);

          AstNodeExpr* index;
          if(AstArraySel* const arrselp = VN_CAST(lhsp, ArraySel)) {
            v3info("into the index - " << array_sel);
            index = arrselp->bitp()->cloneTreePure(false);
          } else {
            v3info("into the const - " << array_sel);
            // make index the index corresponding to resetRdpIt as an array sel
            index = new AstConst(flp, array_sel++); // new ast const as part of an ast expr
          }
          v3info("what the fuck - " << array_sel); // jmc| v3info will only show exact same string once :(

          resetRdp->lhsp()->foreach([=, this](AstNodeVarRef* refp) {
              if (refp->access() != VAccess::WRITE) return;
              AstVarScope* const vscp = refp->varScopep();

              // JMC| I think because each refp has isContinously evaluate to false, nothing ends up changed
              AstVarScope* const newVscp
                  = vscp->varp()->isContinuously() ? getForceComponents(vscp).m_rdVscp : vscp;

              // Disable BLKANDNBLK for this reference
              FileLine* const flp = new FileLine{refp->fileline()};
              flp->warnOff(V3ErrorCode::BLKANDNBLK, true);

              if(VN_IS(vscp->varp()->dtypeSkipRefp(), UnpackArrayDType)) {
               AstArraySel* newpRefp =
                  new AstArraySel{ flp, new AstVarRef{flp, newVscp, VAccess::WRITE }, index->cloneTreePure(false)};
                refp->replaceWith(newpRefp);
                VL_DO_DANGLING(refp->deleteTree(), refp);
              } else {
                AstVarRef* newpRefp =
                  new AstVarRef{flp, newVscp, VAccess::WRITE};
                refp->replaceWith(newpRefp);
                VL_DO_DANGLING(refp->deleteTree(), refp);
              }

          });

        // TODO jmc| maybe should change these to foreach loops and not foreach lambdas
        resetRdp->rhsp()->foreach([=, this](AstNodeVarRef* refp) {
            v3info("rhsp lambda iter");
            if (refp->access() != VAccess::WRITE) {
              v3info("early return form rhsp lambda");
              return;
            }
            AstVarScope* const vscp = refp->varScopep();
            FileLine* const flp = new FileLine{refp->fileline()};
            AstVarRef* const newpRefp = new AstVarRef{refp->fileline(), vscp, VAccess::READ};
            newpRefp->user2(1);  // Don't replace this read ref with the read signal
            if (vscp->varp()->isContinuously()) {
                refp->replaceWith(newpRefp);
            } else if(VN_IS(vscp->varp()->dtypeSkipRefp(), UnpackArrayDType)) {
              if(isRangedDType(vscp)) {
                refp->replaceWith(new AstOr{
                    flp,
                    new AstAnd{flp,
                      new AstArraySel{flp, new AstVarRef{flp, getForceComponents(vscp).m_enVscp, VAccess::READ},  index->cloneTreePure(false)},
                      new AstArraySel{flp, new AstVarRef{flp, getForceComponents(vscp).m_valVscp, VAccess::READ}, index->cloneTreePure(false)}
                      },
                    new AstAnd{flp,
                      new AstNot{flp, new AstArraySel{flp, new AstVarRef{flp, getForceComponents(vscp).m_enVscp, VAccess::READ}, index->cloneTreePure(false)}},
                      new AstArraySel{flp, newpRefp, index->cloneTreePure(false)}
                      }
                    });
              } else {
                refp->replaceWith(new AstCond{
                    flp,
                    new AstArraySel{flp, new AstVarRef{flp, getForceComponents(vscp).m_enVscp, VAccess::READ}, index->cloneTreePure(false)},
                    new AstArraySel{flp, new AstVarRef{flp, getForceComponents(vscp).m_valVscp, VAccess::READ}, index->cloneTreePure(false)},
                    new AstArraySel{flp, newpRefp, index->cloneTreePure(false)}
                    });
              }
            }  else if (isRangedDType(vscp)) { // TODO this check might be problematic in the unpack array case, same as constructor for forceEn was
                refp->replaceWith(new AstOr{
                    flp,
                    new AstAnd{
                        flp, new AstVarRef{flp, getForceComponents(vscp).m_enVscp, VAccess::READ},
                        new AstVarRef{flp, getForceComponents(vscp).m_valVscp, VAccess::READ}},
                    new AstAnd{
                        flp,
                        new AstNot{flp, new AstVarRef{flp, getForceComponents(vscp).m_enVscp,
                                                      VAccess::READ}},
                        newpRefp}});
            }else {
                refp->replaceWith(new AstCond{
                    flp, new AstVarRef{flp, getForceComponents(vscp).m_enVscp, VAccess::READ},
                    new AstVarRef{flp, getForceComponents(vscp).m_valVscp, VAccess::READ},
                    newpRefp});
            }
            VL_DO_DANGLING(refp->deleteTree(), refp);
        });
        }

        for(int idx = 1; idx < resetRdp_vec.size(); idx++)
          resetRdp_vec[0]->addNext(resetRdp_vec[idx]);
        resetRdp_vec[0]->addNext(resetEnp);
        relinker.relink(resetRdp_vec[0]);
    }

    void visit(AstVarScope* nodep) override {
        // If this signal is marked externally forceable, create the public force signals
        if (nodep->varp()->isForceable()) {
            const ForceComponentsVarScope& fc = getForceComponents(nodep);
            fc.m_enVscp->varp()->sigUserRWPublic(true);
            fc.m_valVscp->varp()->sigUserRWPublic(true);
        }
    }

    // CONSTRUCTOR
    explicit ForceConvertVisitor(AstNetlist* nodep) {
        // Transform all force and release statements
        iterateAndNextNull(nodep->modulesp());

        // Replace references to forced signals
        nodep->modulesp()->foreachAndNext([this](AstVarRef* nodep) {
            if (ForceComponentsVarScope* const fcp
                = m_forceComponentsVarScope.tryGet(nodep->varScopep())) {
                switch (nodep->access()) {
                case VAccess::READ:
                    // Read references replaced to read the new, possibly forced signal
                    if (!nodep->user2()) {
                        nodep->varp(fcp->m_rdVscp->varp());
                        nodep->varScopep(fcp->m_rdVscp);
                    }
                    break;
                case VAccess::WRITE:
                    // Write references use the original signal
                    break;
                default:
                    nodep->v3error(
                        "Unsupported: Signals used via read-write reference cannot be forced");
                    break;
                }
            }
        });
    }

public:
    static void apply(AstNetlist* nodep) { ForceConvertVisitor{nodep}; }
};

//######################################################################
//

void V3Force::forceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    if (!v3Global.hasForceableSignals()) return;
    ForceConvertVisitor::apply(nodep);
    V3Global::dumpCheckGlobalTree("force", 0, dumpTreeEitherLevel() >= 3);
}
