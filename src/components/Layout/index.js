import {
  alignItems,
  justifyContent,
  flexGrow,
  flexWrap,
  flexBasis,
  flexDirection,
  complexStyle,
} from 'styled-system';
import { applyDefaultStyles } from '../../utils/styling';
import styled from '../../kfFeels/kfReactEmotion';

const boxStyles = complexStyle({
  prop: 'boxStyle',
  key: 'boxStyles',
});
console.log(applyDefaultStyles);
export const Box = styled(applyDefaultStyles('div'))`
  ${boxStyles};
`;

const flexStyles = complexStyle({
  prop: 'flexStyle',
  key: 'flexStyles',
});
export const Flex = styled(Box)`
  display: flex;
  ${flexStyles};
  ${alignItems};
  ${justifyContent};
  ${flexWrap};
  ${flexBasis};
  ${flexDirection};
  ${flexGrow};
`;
