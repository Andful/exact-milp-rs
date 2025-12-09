use num::rational::Ratio;
use scip_sys::*;
use std::ffi::CString;
use std::ffi::c_uint;
use std::mem::ManuallyDrop;
use std::os::unix::ffi::OsStrExt;
use std::path::Path;
use std::ptr::NonNull;
use std::ptr::null_mut;

pub enum ConshdlrResult {
    /// States that the problem is feasible.
    Feasible,
    /// States that the problem is infeasible.
    CutOff,
    /// Added another constraint that resolves the infeasibility.
    ConsAdded,
    /// Reduced the domain of a variable.
    ReducedDom,
    /// Added a cutting plane that separates the lp solution.
    Separated,
    /// Request to resolve the LP.
    SolveLP,
    /// Created a branching.
    Branched,
}

impl From<ConshdlrResult> for SCIP_Result {
    fn from(result: ConshdlrResult) -> Self {
        match result {
            ConshdlrResult::Feasible => SCIP_Result_SCIP_FEASIBLE,
            ConshdlrResult::CutOff => SCIP_Result_SCIP_CUTOFF,
            ConshdlrResult::ConsAdded => SCIP_Result_SCIP_CONSADDED,
            ConshdlrResult::ReducedDom => SCIP_Result_SCIP_REDUCEDDOM,
            ConshdlrResult::Separated => SCIP_Result_SCIP_SEPARATED,
            ConshdlrResult::SolveLP => SCIP_Result_SCIP_SOLVELP,
            ConshdlrResult::Branched => SCIP_Result_SCIP_BRANCHED,
        }
    }
}

pub trait Conshdlr {
    // Required methods
    fn check<'brand>(
        &mut self,
        problem: &Problem<'brand>,
        solution: &Solution<'_, 'brand>
    ) -> bool;
    fn enforce<'brand>(
        &mut self,
        problem: &Problem<'brand>
    ) -> ConshdlrResult;
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Status {
    Unknown,
    UserInterrupt,
    NodeLimit,
    TotalNodeLimit,
    StallNodeLimit,
    TimeLimit,
    MemoryLimit,
    GapLimit,
    PrimalLimit,
    DualLimit,
    SolutionLimit,
    BestSolutionLimit,
    RestartLimit,
    Optimal,
    Infeasible,
    Unbounded,
    Inforunbd,
    Terminate,
}

impl From<SCIP_Status> for Status {
    /// Converts a u32 value to a `Status` enum variant.
    fn from(val: SCIP_Status) -> Self {
        match val {
            SCIP_Status_SCIP_STATUS_UNKNOWN => Status::Unknown,
            SCIP_Status_SCIP_STATUS_USERINTERRUPT => Status::UserInterrupt,
            SCIP_Status_SCIP_STATUS_NODELIMIT => Status::NodeLimit,
            SCIP_Status_SCIP_STATUS_TOTALNODELIMIT => Status::TotalNodeLimit,
            SCIP_Status_SCIP_STATUS_STALLNODELIMIT => Status::StallNodeLimit,
            SCIP_Status_SCIP_STATUS_TIMELIMIT => Status::TimeLimit,
            SCIP_Status_SCIP_STATUS_MEMLIMIT => Status::MemoryLimit,
            SCIP_Status_SCIP_STATUS_GAPLIMIT => Status::GapLimit,
            SCIP_Status_SCIP_STATUS_PRIMALLIMIT => Status::PrimalLimit,
            SCIP_Status_SCIP_STATUS_DUALLIMIT => Status::DualLimit,
            SCIP_Status_SCIP_STATUS_SOLLIMIT => Status::SolutionLimit,
            SCIP_Status_SCIP_STATUS_BESTSOLLIMIT => Status::BestSolutionLimit,
            SCIP_Status_SCIP_STATUS_RESTARTLIMIT => Status::RestartLimit,
            SCIP_Status_SCIP_STATUS_OPTIMAL => Status::Optimal,
            SCIP_Status_SCIP_STATUS_INFEASIBLE => Status::Infeasible,
            SCIP_Status_SCIP_STATUS_UNBOUNDED => Status::Unbounded,
            SCIP_Status_SCIP_STATUS_INFORUNBD => Status::Inforunbd,
            SCIP_Status_SCIP_STATUS_TERMINATE => Status::Terminate,
            _ => panic!("Unknown SCIP status {val:?}"),
        }
    }
}

type InvariantLifetime<'brand> = std::marker::PhantomData<fn(&'brand ()) -> &'brand ()>;

pub struct Solution<'a, 'brand> {
    problem: &'a Problem<'brand>,
    sol: NonNull<SCIP_SOL>,
}

impl<'a, 'brand> Solution<'a, 'brand> {
    pub fn value(&self, var: Var<'brand>) -> Ratio<isize> {
        let mut res: *mut SCIP_Rational = null_mut();
        unsafe {
            SCIPrationalCreate(&mut res);

            SCIPgetSolValExact(
                self.problem.scip.as_ptr(),
                self.sol.as_ptr(),
                var.var.as_ptr(),
                res,
            );
            let result = Ratio::new(
                SCIPrationalNumerator(res) as isize,
                SCIPrationalDenominator(res) as isize,
            );
            SCIPrationalFree(&mut res);
            result
        }
    }
}

pub struct Problem<'brand> {
    scip: NonNull<SCIP>,
    vars: Vec<NonNull<SCIP_Var>>,
    cons: Vec<NonNull<SCIP_Cons>>,
    _marker: InvariantLifetime<'brand>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct Var<'brand> {
    var: NonNull<SCIP_Var>,
    _marker: InvariantLifetime<'brand>,
}

pub struct VarBuilder<'a, 'brand> {
    problem: &'a Problem<'brand>,
    var: NonNull<SCIP_Var>,
    _marker: InvariantLifetime<'brand>,
}

impl<'a, 'brand> VarBuilder<'a, 'brand> {
    pub fn lb(self, lb: Ratio<isize>) -> Self {
        let mut new_lb: *mut SCIP_Rational = null_mut();
        unsafe {
            SCIPrationalCreate(&mut new_lb);
            SCIPrationalSetFraction(new_lb, *lb.numer() as i64, *lb.denom() as i64);
            SCIPchgVarLbExact(self.problem.scip.as_ptr(), self.var.as_ptr(), new_lb);
            SCIPrationalFree(&mut new_lb);
        };
        self
    }

    pub fn ub(self, ub: Ratio<isize>) -> Self {
        let mut new_ub: *mut SCIP_Rational = null_mut();
        unsafe {
            SCIPrationalCreate(&mut new_ub);
            SCIPrationalSetFraction(new_ub, *ub.numer() as i64, *ub.denom() as i64);
            SCIPchgVarUbExact(self.problem.scip.as_ptr(), self.var.as_ptr(), new_ub);
            SCIPrationalFree(&mut new_ub);
        };
        self
    }

    pub fn obj(self, obj: Ratio<isize>) -> Self {
        let mut new_obj: *mut SCIP_Rational = null_mut();
        unsafe {
            SCIPrationalCreate(&mut new_obj);
            SCIPrationalSetFraction(new_obj, *obj.numer() as i64, *obj.denom() as i64);
            SCIPchgVarObjExact(self.problem.scip.as_ptr(), self.var.as_ptr(), new_obj);
            SCIPrationalFree(&mut new_obj);
        };
        self
    }

    pub fn integer(self) -> Self {
        let mut _b: c_uint = 0;
        unsafe {
            SCIPchgVarType(
                self.problem.scip.as_ptr(),
                self.var.as_ptr(),
                SCIP_Vartype_SCIP_VARTYPE_INTEGER,
                &mut _b,
            );
        }
        self
    }

    pub fn build(self) -> Var<'brand> {
        let Self { var, .. } = self;
        unsafe { SCIPaddVar(self.problem.scip.as_ptr(), var.as_ptr()) };
        Var {
            var,
            _marker: Default::default(),
        }
    }
}

impl<'brand> Problem<'brand> {
    pub fn new<R, F>(name: &str, fun: F) -> R
    where
        for<'new_brand> F: FnOnce(&mut Problem<'new_brand>) -> R,
    {
        let mut scip = null_mut();

        unsafe {
            SCIPcreate(&mut scip);
            SCIPincludeDefaultPlugins(scip);
            SCIPenableExactSolving(scip, 1);
            SCIPcreateProbBasic(scip, CString::new(name).unwrap().as_ptr());
        };

        let mut problem = Self {
            scip: NonNull::new(scip).unwrap(),
            vars: Vec::new(),
            cons: Vec::new(),
            _marker: InvariantLifetime::default(),
        };

        let result = fun(&mut problem);

        let Self {
            scip, vars, cons, ..
        } = problem;
        for mut c in cons.into_iter().map(|c| c.as_ptr()) {
            unsafe { SCIPreleaseCons(scip.as_ptr(), &mut c) };
        }
        for mut v in vars.into_iter().map(|v| v.as_ptr()) {
            unsafe {
                SCIPreleaseVar(scip.as_ptr(), &mut v);
            };
        }
        unsafe { SCIPfree(&mut scip.as_ptr()) };

        result
    }

    pub fn var(&mut self, name: &str) -> VarBuilder<'_, 'brand> {
        let mut var: *mut SCIP_Var = null_mut();
        unsafe {
            SCIPcreateVarBasic(
                self.scip.as_ptr(),
                &mut var,
                CString::new(name).unwrap().as_c_str().as_ptr(),
                -SCIPinfinity(self.scip.as_ptr()),
                SCIPinfinity(self.scip.as_ptr()),
                0.0,
                SCIP_Vartype_SCIP_VARTYPE_CONTINUOUS,
            );
            SCIPaddVarExactData(self.scip.as_ptr(), var, null_mut(), null_mut(), null_mut());
        };

        let var = NonNull::new(var).unwrap();

        self.vars.push(var);

        VarBuilder {
            var,
            problem: self,
            _marker: Default::default(),
        }
    }

    pub fn add_constraint(
        &mut self,
        name: &str,
        lhs: Option<Ratio<isize>>,
        vals: &[Ratio<isize>],
        vars: &[Var<'brand>],
        rhs: Option<Ratio<isize>>,
    ) {
        assert_eq!(vals.len(), vars.len());
        let mut cons = null_mut();
        let mut rationals: *mut *mut SCIP_RATIONAL = null_mut();
        unsafe {
            SCIPrationalCreateArray(&mut rationals, vals.len() as i32 + 2);
            let lhs_rational = *rationals.offset(vals.len() as isize);
            if let Some(lhs) = lhs {
                SCIPrationalSetFraction(lhs_rational, *lhs.numer() as i64, *lhs.denom() as i64);
            } else {
                SCIPrationalSetNegInfinity(lhs_rational);
            }
            let rhs_rational = *rationals.offset(vals.len() as isize + 1);
            if let Some(rhs) = rhs {
                SCIPrationalSetFraction(rhs_rational, *rhs.numer() as i64, *rhs.denom() as i64);
            } else {
                SCIPrationalSetInfinity(rhs_rational);
            }
            for i in 0..vals.len() {
                SCIPrationalSetFraction(
                    *rationals.offset(i as isize),
                    *vals[i].numer() as i64,
                    *vals[i].denom() as i64,
                );
            }
            SCIPcreateConsBasicExactLinear(
                self.scip.as_ptr(),
                &mut cons,
                CString::new(name).unwrap().as_c_str().as_ptr(),
                vars.len() as i32,
                vars.iter()
                    .map(|e| e.var.as_ptr())
                    .collect::<Vec<_>>()
                    .as_mut_ptr(),
                rationals,
                lhs_rational,
                rhs_rational,
            );
            SCIPrationalFreeArray(&mut rationals, vals.len() as i32 + 2);

            SCIPaddCons(self.scip.as_ptr(), cons);
        }
        self.cons.push(NonNull::new(cons).unwrap());
    }

    pub fn solve(&self) -> Option<Solution<'_, 'brand>> {
        let solution: *mut SCIP_SOL = unsafe {
            SCIPsolve(self.scip.as_ptr());
            SCIPgetBestSol(self.scip.as_ptr())
        };

        NonNull::new(solution).map(|sol| Solution { problem: self, sol })
    }

    pub fn get_best_solution(&self) -> Option<Solution<'_, 'brand>> {
        let solution: *mut SCIP_SOL = unsafe {
            SCIPgetBestSol(self.scip.as_ptr())
        };

        NonNull::new(solution).map(|sol| Solution { problem: self, sol })
    }

    pub fn status(&self) -> Status {
        let status = unsafe { SCIPgetStatus(self.scip.as_ptr()) };
        status.into()
    }

    pub fn set_bool_param(&self, param: &str, value: bool) {
        let param = CString::new(param).unwrap();
        unsafe {
            SCIPsetBoolParam(
                self.scip.as_ptr(),
                param.as_ptr(),
                if value { 1u32 } else { 0u32 },
            )
        };
    }

    pub fn set_int_param(&self, param: &str, value: i32) {
        let param = CString::new(param).unwrap();
        unsafe { SCIPsetIntParam(self.scip.as_ptr(), param.as_ptr(), value) };
    }

    pub fn set_longint_param(&self, param: &str, value: i64) {
        let param = CString::new(param).unwrap();
        unsafe { SCIPsetLongintParam(self.scip.as_ptr(), param.as_ptr(), value) };
    }

    pub fn set_real_param(&self, param: &str, value: f64) {
        let param = CString::new(param).unwrap();
        unsafe { SCIPsetRealParam(self.scip.as_ptr(), param.as_ptr(), value) };
    }

    pub fn export(&self, path: &Path) {
        unsafe {
            SCIPwriteOrigProblem(
                self.scip.as_ptr(),
                CString::new(path.as_os_str().as_bytes())
                    .ok()
                    .unwrap()
                    .as_ptr(),
                c"lp".as_ptr(),
                FALSE,
            );
        }
    }

    pub fn include_conshdlr<'a, C: Conshdlr + 'a>(
        &'a self,
        name: &str,
        desc: &str,
        enfopriority: i32,
        checkpriority: i32,
        conshdlr: &'a C,
    ) {
        let c_name = CString::new(name).unwrap();
        let c_desc = CString::new(desc).unwrap();

        extern "C" fn consenfolp<'brand, C: Conshdlr>(
            scip: *mut SCIP,
            conshdlr: *mut SCIP_CONSHDLR,
            _conss: *mut *mut SCIP_CONS,
            _nconss: std::os::raw::c_int,
            _nusefulconss: std::os::raw::c_int,
            _solinfeasible: std::os::raw::c_uint,
            result: *mut SCIP_RESULT,
        ) -> SCIP_RETCODE {
            let problem = ManuallyDrop::new(Problem {
                scip: NonNull::new(scip).unwrap(),
                vars: vec![],
                cons: vec![],
                _marker: Default::default()
            });
            let data_ptr = unsafe { SCIPconshdlrGetData(conshdlr) };
            assert!(!data_ptr.is_null());
            let conshdlr_ptr = data_ptr as *mut C;

            unsafe {
                *result = (*conshdlr_ptr).enforce(&problem).into();
            }

            SCIP_Retcode_SCIP_OKAY
        }

        extern "C" fn conscheck<'brand, C: Conshdlr>(
            scip: *mut SCIP,
            conshdlr: *mut SCIP_CONSHDLR,
            _conss: *mut *mut SCIP_CONS,
            _nconss: ::std::os::raw::c_int,
            sol: *mut SCIP_SOL,
            _checkintegrality: ::std::os::raw::c_uint,
            _checklprows: ::std::os::raw::c_uint,
            _printreason: ::std::os::raw::c_uint,
            _completely: ::std::os::raw::c_uint,
            result: *mut SCIP_RESULT,
        ) -> SCIP_RETCODE {
            let problem = ManuallyDrop::new(Problem {
                scip: NonNull::new(scip).unwrap(),
                vars: vec![],
                cons: vec![],
                _marker: Default::default()
            });
            let solution = ManuallyDrop::new(Solution {
                problem: &problem,
                sol: NonNull::new(sol).unwrap(),
            });
            let data_ptr = unsafe { SCIPconshdlrGetData(conshdlr) };
            assert!(!data_ptr.is_null());
            let conshdlr_ptr = data_ptr as *mut C;

            let feasible = unsafe { (*conshdlr_ptr).check(&problem, &solution).into() };

            unsafe {
                *result = if feasible {
                    SCIP_Result_SCIP_FEASIBLE
                } else {
                    SCIP_Result_SCIP_INFEASIBLE
                };
            }

            SCIP_Retcode_SCIP_OKAY
        }

        extern "C" fn conslock(
            _scip: *mut SCIP,
            _conshdlr: *mut SCIP_CONSHDLR,
            _cons: *mut SCIP_CONS,
            _locktype: SCIP_LOCKTYPE,
            _nlockspos: ::std::os::raw::c_int,
            _nlocksneg: ::std::os::raw::c_int,
        ) -> SCIP_RETCODE {
            SCIP_Retcode_SCIP_OKAY
        }

        extern "C" fn consfree(
            _scip: *mut SCIP,
            _conshdlr: *mut SCIP_CONSHDLR,
        ) -> SCIP_Retcode {
            SCIP_Retcode_SCIP_OKAY
        }

        let ptr = Box::into_raw(Box::new(conshdlr));
        let cons_faker = ptr as *mut SCIP_CONSHDLRDATA;

        let mut conshdlr: *mut SCIP_CONSHDLR = std::ptr::null_mut();

        unsafe {
            SCIPincludeConshdlrBasic(
                self.scip.as_ptr(),
                &mut conshdlr,
                c_name.as_ptr(),
                c_desc.as_ptr(),
                enfopriority,
                checkpriority,
                0,
                false.into(),
                Some(consenfolp::<C>),
                None,
                Some(conscheck::<C>),
                Some(conslock),
                cons_faker,
            );
        }

        unsafe { SCIPsetConshdlrFree(self.scip.as_ptr(), conshdlr, Some(consfree)); }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test1() {
        Problem::new("problem", |problem| {
            // eample from https://www.mathsisfun.com/algebra/linear-programming.html
            let b = problem
                .var("b")
                .obj(Ratio::from_integer(-300))
                .integer()
                .build();
            let s = problem
                .var("s")
                .obj(Ratio::from_integer(-350))
                .integer()
                .build();

            problem.add_constraint(
                "c1",
                None,
                &[Ratio::from_integer(5), Ratio::from_integer(4)],
                &[b, s],
                Some(Ratio::from_integer(80)),
            );

            problem.add_constraint(
                "c2",
                None,
                &[Ratio::from_integer(3), Ratio::from_integer(4)],
                &[b, s],
                Some(Ratio::from_integer(60)),
            );

            let solution = problem.solve().unwrap();

            //problem.export(&Path::new("test.lp"));

            println!("b:{} s:{}", solution.value(b), solution.value(s));
        });
    }
}
