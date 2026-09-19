import type { BallScene, Scenario } from '../core';
import { distanceProfile } from './distance-profile';
import './semantic-views.css';

const number = (value: number) => Number(value.toPrecision(5)).toString();

export function DistanceProfileView({ scene, scenario }: { scene: BallScene; scenario: Scenario }) {
  const profile = distanceProfile(scene, scenario);
  if (profile.status === 'unknown') return <div className="sv-profile-empty"><h3>Distance across all coordinates</h3><p>{profile.reason}</p><p>The coordinate slice remains available even when no numerical representative is chosen.</p></div>;
  const maxDisplacement = Math.max(...profile.absoluteDisplacements);
  const extent = maxDisplacement || 1;
  const barWidth = 650 / profile.dimension;
  const pointName = scene.point?.kind === 'var' ? scene.point.name : 'P';
  const relation = scene.boundary === 'open' ? '<' : scene.boundary === 'closed' ? '≤' : '=';
  const ticks = [...new Set([0, Math.floor((profile.dimension - 1) / 4), Math.floor((profile.dimension - 1) / 2), Math.floor((profile.dimension - 1) * 3 / 4), profile.dimension - 1])];
  return <div className="sv-distance-profile">
    <div className="sv-profile-summary"><div><span className="sv-small-label">Full {profile.dimension}-coordinate distance</span><strong>dist({pointName}, c) = {number(profile.distance)}</strong><span>{profile.metric === 'L2' ? 'Square root of the sum of squared coordinate displacements' : 'Maximum absolute coordinate displacement'}</span></div><div><span className="sv-small-label">Region condition</span><strong>d {relation} {number(profile.radius)}</strong><span>{profile.membership?.status === 'true' ? 'Satisfied at this numerical sample' : profile.membership?.status === 'false' ? 'Not satisfied at this numerical sample' : 'No reliable numerical comparison'}</span></div></div>
    <svg className="sv-profile-plot" viewBox="0 0 760 305" role="img" aria-label={`Absolute displacement in all ${profile.dimension} coordinates; ${profile.metric} distance ${number(profile.distance)}`}>
      <title>All coordinate displacements of {pointName} from the center</title>
      <rect width="760" height="305" fill="#fafcfb"/>
      <text x="64" y="31" className="sv-profile-label">|{pointName}ᵢ − cᵢ|</text>
      {[0, 0.5, 1].map(fraction => <g key={fraction}><path d={`M64 ${240 - fraction * 175} H714`} stroke="#e2e9ec" strokeWidth="1"/><text x="52" y={244 - fraction * 175} textAnchor="end" className="sv-profile-label">{number(fraction * extent)}</text></g>)}
      {profile.absoluteDisplacements.map((value, index) => <rect key={index} x={64 + index * barWidth + Math.min(1, barWidth * 0.12)} y={240 - value / extent * 175} width={Math.max(0.8, barWidth - Math.min(2, barWidth * 0.24))} height={Math.max(value === 0 ? 1 : 0, value / extent * 175)} rx={Math.min(2, barWidth * 0.1)} fill={value === 0 ? '#ccdcd9' : '#528d80'}><title>Coordinate {index + 1}: {number(value)}</title></rect>)}
      {ticks.map(index => <text key={index} x={64 + (index + 0.5) * barWidth} y="265" textAnchor="middle" className="sv-profile-label">{index + 1}</text>)}
      <text x="389" y="291" textAnchor="middle" className="sv-profile-label">Coordinate index · all {profile.dimension} coordinates shown</text>
    </svg>
    <p className="sv-view-note">The bars measure one representative point in the full ambient space. They discard displacement signs and do not depict the shape of the region. The coordinate slice shows a different, explicitly chosen intersection.</p>
  </div>;
}
