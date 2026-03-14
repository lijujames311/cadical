#include "internal.hpp"

namespace CaDiCaL {

void Internal::copy_phases (vector<signed char> &dst) {
  START (copy);
  for (auto i : vars) {
    const signed char tmp = phases.saved[i.var ()];
    if (tmp)
      dst[i.var ()] = tmp;
  }
  STOP (copy);
}

void Internal::save_assigned_phases (vector<signed char> &dst) {
  START (copy);
  for (auto l : trail) {
    // discussion with Armin and Florian to only save value excluding
    // the ones that lead to the conflict to avoid the order of
    // propagation to lead to different conflicts.
    if (var (l).level < level)
      dst[vidx (l)] = vals[vidx (l)];
  }
  STOP (copy);
}

void Internal::clear_phases (vector<signed char> &dst) {
  START (copy);
  for (auto i : vars)
    dst[i.var ()] = 0;
  STOP (copy);
}

void Internal::phase (Lit lit) {
  const int idx = vidx (lit);
  signed char old_forced_phase = phases.forced[idx];
  signed char new_forced_phase = sign (lit);
  if (old_forced_phase == new_forced_phase) {
    LOG ("forced phase remains at %s", LOGLIT(lit));
    return;
  }
  if (old_forced_phase)
    LOG ("overwriting old forced phase %s", LOGLIT(lit));
  LOG ("new forced phase %s", LOGLIT(lit));
  phases.forced[idx] = new_forced_phase;
}

void Internal::unphase (Lit lit) {
  const int idx = vidx (lit);
  signed char old_forced_phase = phases.forced[idx];
  if (!old_forced_phase) {
    LOG ("forced phase of %s already reset", LOGLIT(lit));
    return;
  }
  LOG ("clearing old forced phase %s", LOGLIT(lit));
  phases.forced[idx] = 0;
}

} // namespace CaDiCaL
